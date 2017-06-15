module Clustering

open FSharp.Collections.ParallelSeq

type Cluster (stateSeq : Features.Environment seq) =
    let stateSet = new System.Collections.Generic.HashSet<Features.Environment>(stateSeq)
    let mutable hashCodeCache = None

    member __.States with get () : Features.Environment seq = stateSet :> _
    member __.Size with get () = stateSet.Count
    member __.IsEmpty with get () = stateSet.Count = 0

    member __.Clone () =
        new Cluster(new System.Collections.Generic.HashSet<Features.Environment>(stateSet))

    member __.Remove e =
        hashCodeCache <- None
        stateSet.Remove e |> ignore
    member __.Add e =
        hashCodeCache <- None
        stateSet.Add e |> ignore

    override __.Equals other =
        match other with
        | :? Cluster as otherCluster->
            stateSet.SetEquals otherCluster.States
        | _ -> false
    override self.GetHashCode () =
        if hashCodeCache.IsNone then
            //Ignore order in Sequence, so use commutative operation:
            hashCodeCache <- Some (Seq.fold (fun h n -> h ^^^ n.GetHashCode()) 0 self.States)
        hashCodeCache.Value

    new () = Cluster (Seq.empty)

    static member Empty = new Cluster()

type Clusters = System.Collections.Generic.Dictionary<int, Cluster>

//// Actual k-means clustering:
// Following code copied from https://github.com/mathias-brandewinder/Machine-Learning-In-Action

// the Distance between 2 observations 'a is a float
// It also better be positive - left to the implementer
type Distance<'a> = 'a -> 'a -> float
// CentroidsFactory, given a dataset,
// should generate n Centroids
type CentroidsFactory<'a> = System.Collections.Generic.List<'a> -> int -> 'a list
// Given a Centroid and observations in a Cluster,
// create an updated Centroid
type ToCentroid<'a> = 'a -> 'a seq -> 'a

// Returns the index of and distance to the
// Centroid closest to observation
let closest (dist: Distance<'a>) centroids (obs: 'a) =
    let mutable (idx, minIdx, min) = (0, 0, System.Double.MaxValue)
    for c in centroids do
        let d = dist c obs
        if d < min then
            min <- d
            minIdx <- idx
        idx <- idx + 1
    (minIdx, min)

// Euclidean distance between 2 points, represented as float []
let euclidean x y =
    Array.fold2 (fun d e1 e2 -> d + pown (e1 - e2) 2) 0. x y
    |> sqrt

// Picks k random observations as initial centroids
// (this is very lazy, even tolerates duplicates)
let randomCentroids<'a> (rng: System.Random)
                        (sample: System.Collections.Generic.List<'a>)
                        k =
    let size = sample.Count
    [ for _ in 1 .. k do yield sample.[rng.Next(size)] ]

// Recompute Centroid as average of given sample
let avgCentroid (current: float []) (sample: float [] seq) =
    let size = Seq.length sample
    match size with
    | 0 -> current
    | _ ->
        sample
        |> Seq.reduce (fun v1 v2 ->
               Array.map2 (fun v1x v2x -> v1x + v2x) v1 v2)
        |> Array.map (fun e -> e / (float)size)

// Given a distance, centroid factory and
// centroid aggregation function, 
// return mapping of inputs to clusters
let kmeans (dist: Distance<'a>)
           (factory: CentroidsFactory<'a>)
           (aggregator: ToCentroid<'a>)
           (dataset: System.Collections.Generic.List<'a>)
           k =
    // Recursively update Centroids and
    // the assignment of observations to Centroids
    let rec update (centroids, assignment) =
        // Assign each point to the closest centroid
        let next =
            dataset
            |> Seq.map (fun obs -> (obs, closest dist centroids obs))
            |> Seq.toList
        // Check if any assignment changed
        let change =
            match assignment with
            | Some(previous) ->
                Seq.zip previous next
                |> Seq.exists (fun ((_, (i, _)), (_, (j, _))) -> i <> j)
            | None -> true // initially we have no assignment
        if change
        then
            // Update each Centroid position:
            // extract cluster of points assigned to each Centroid
            // and compute the new Centroid by aggregating cluster
            let updatedCentroids =
                centroids
                |> Seq.mapi (fun i centroid ->
                    next
                    |> Seq.fold (fun res (obs, (ci, _)) -> if ci = i then obs :: res else res) []
                    |> aggregator centroid)
            // Perform another round of updates
            update (updatedCentroids, Some(next))
        // No assignment changed, we are done
        else (centroids, next)

    let initialCentroids = factory dataset k
    update (initialCentroids, None) |> snd

//// ------ end copied code -------

type ClusterSet (clusterSeq : Cluster seq) =
    let clusterSet = new System.Collections.Generic.HashSet<Cluster>(clusterSeq)
    let mutable hashCodeCache = None

    member __.Clusters with get () : Cluster seq = clusterSet :> _

    member __.Add e =
        hashCodeCache <- None
        clusterSet.Add e |> ignore

    override __.Equals other =
        match other with
        | :? ClusterSet as otherCluster->
            clusterSet.SetEquals otherCluster.Clusters
        | _ -> false
    override self.GetHashCode () =
        if hashCodeCache.IsNone then
            //Ignore order in Sequence, so use commutative operation:
            hashCodeCache <- Some (Seq.fold (fun h n -> h ^^^ n.GetHashCode()) 0 self.Clusters)
        hashCodeCache.Value

    static member Empty = new ClusterSet(Seq.empty)

let featureCluster (envs: Features.Environment list) mlmodelwrapper insertBtwns debug =
    // Get list of variables we care about
    let vars =
        envs
        |> List.head |> snd
        |> Map.fold (fun vars v _ -> match v with | SepLogic.VarAddr vname -> vname :: vars | _ -> vars) []
    if debug then
        printfn "Considering reachability between: %s" <| String.concat ", " vars

    // Convert envs to feature vectors
    let envs = System.Collections.Generic.List(envs)
    let envVectors = System.Collections.Generic.List(envs |> Seq.map (Features.GetReachabilityFeatures vars))
    let numEnvs = envs.Count - 1
    let envToId = System.Collections.Generic.Dictionary()
    envs |> Seq.iteri (fun i e -> envToId.[e] <- i)
    let clusterToString (cluster: Cluster) =
        (cluster.States
            |> Seq.map (fun e -> envToId.[e]) |> Seq.sort
            |> Seq.map (fun idx -> sprintf "%02i" idx)
            |> String.concat "," |> sprintf "[%s]")

    if debug then
        for u in vars do
            for v in vars do
                printf "(%s, %s) " u v
        printfn ""
        for i in 0 .. numEnvs do
            printfn "%d: %A" i envVectors.[i]
        printfn "\n"

    let classifierToClusters (numClusters : int) (samplesToClusterIdList : (float[] * (int * 'b)) list) =
        let sampleToClusterId = System.Collections.Generic.Dictionary()
        for (sample, (clusterId, _)) in samplesToClusterIdList do
            sampleToClusterId.Add (sample, clusterId)

        let clusters = seq { for _ in 1..numClusters do yield Cluster() } |> Array.ofSeq
        for i in 0 .. numEnvs do
            clusters.[sampleToClusterId.[envVectors.[i]]].Add envs.[i]

        let clusterSet = ClusterSet.Empty
        clusters |> Seq.iter clusterSet.Add
        clusterSet

    let printClusters (clusters: ClusterSet) =
        let getPredOfStates envs =
            Predictor.PredictSyntaxTree mlmodelwrapper envs 5 false insertBtwns false
            |> snd
            |> List.maxBy (snd >> snd) // Pick most likely prediction
            |> snd

        let clusterPreds =
            clusters.Clusters
            |> Seq.filter (fun cluster -> not cluster.IsEmpty)
            |> Seq.map (fun cluster -> (cluster, getPredOfStates (List.ofSeq cluster.States)))
            |> Seq.cache

        if debug then
            printfn "\nClusters:"
            for (cluster, (pred, prob)) in clusterPreds do
                printfn "%s: {p=%.4f}: %s" (clusterToString cluster) prob (string pred)

        let formula =
            clusterPreds
            |> Seq.map (fun (_, (pred, _)) -> string pred)
            |> String.concat " || "
        printfn "Prediction {p=0.0000}: %s" formula

    let doMultipleRunsAndPickBest (numClusters, numRuns) =
        let scoreboard = System.Collections.Concurrent.ConcurrentDictionary()  // clusterSet -> count
        let doRun runId =
            let rng = System.Random runId
            let factory = randomCentroids<float []> rng
            let samplesToClusterId = kmeans euclidean factory avgCentroid envVectors numClusters
            let clusters = classifierToClusters numClusters samplesToClusterId
            scoreboard.AddOrUpdate (clusters, 1, (fun _ count -> count + 1)) |> ignore

        [1..numRuns] |> PSeq.iter doRun
        let _, bestClusters = scoreboard |> Seq.maxBy (fun kv -> kv.Value) |> (fun kv -> kv.Value, kv.Key)
        if debug then
            printfn "\nClustering results after %d runs:" numRuns
            for kv in (scoreboard |> Seq.sortBy (fun kv -> - kv.Value)) do
                printfn "  %d (%.2f): %s" kv.Value (float (kv.Value) / float (numRuns))
                    (kv.Key.Clusters |> Seq.map clusterToString |> String.concat " ")
        bestClusters

    [(2, 1000) ; (3, 1000) ; (4, 1000) ; (5, 1000)]
    |> Seq.map doMultipleRunsAndPickBest
    |> Seq.iter printClusters
    []
