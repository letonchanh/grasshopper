module Features

open Utils
open SyntaxTree

let private Bool2Float b = if b then 1. else 0.

type Value = State.Value
type VarEnvironment = Map<SepLogic.TypedVar, Value>

let varEnvFromVarStack (varStack : State.VarStack) : VarEnvironment =
    varStack |> Seq.map (fun (name, value) -> (SepLogic.VarAddr name, value)) |> Map.ofSeq

let restrictToAddrs (varEnv : VarEnvironment) =
    Map.fold (fun newMap k v -> match v with | (State.ValAddr a) -> Map.add k a newMap | _ -> newMap) Map.empty varEnv

type Environment = HeapGraph * VarEnvironment

let findCommonVars (envs: Environment list) =
    let firstVars = envs |> List.head |> snd |> Map.toSeq |> Seq.map fst |> Set.ofSeq
    envs
    |> List.tail
    |> List.fold (fun vars env ->
        let theseVars = env |> snd |> Map.toSeq |> Seq.map fst |> Set.ofSeq
        Set.intersect theseVars vars
    ) firstVars

let restrictEnvsToCommonVars (envs: Environment list) : Environment list =
    let vars = findCommonVars envs
    envs |> List.map (fun (h, e) -> h, Map.filter (fun v _ -> Set.contains v vars) e)

type [<Sealed>]FeatureToIndexMap() =
    let featureToIndex = new System.Collections.Concurrent.ConcurrentDictionary<string, int>()
    let mutable featureCounter = 0

    override __.ToString () =
        featureToIndex |> Seq.map (fun kv -> System.String.Format("  {0} -> {1}", kv.Key, kv.Value)) |> String.concat "\n"

    member self.NoteFeatures (featureNames : seq<string>) =
        featureNames |> Seq.iter (self.GetFeatureId >> ignore)

    member __.GetFeatureId featureName : int =
        featureToIndex.GetOrAdd
            (featureName,
                new System.Func<string, int>(
                    fun _ ->
                        lock
                            featureToIndex
                            (fun () ->
                                let featureId = featureCounter
                                featureCounter <- featureCounter + 1
                                featureId)))

    member __.GetExistingFeatureId featureName : int option =
        match featureToIndex.TryGetValue featureName with
        | (true, id) -> Some id
        | (false, _) -> None

    member __.Count = featureCounter

    member __.ToJson () =
        [for kv in featureToIndex -> (kv.Key, kv.Value |> decimal |> Chiron.Number)]
        |> Map.ofList |> Chiron.Object

    interface System.Collections.Generic.IEnumerable<System.Collections.Generic.KeyValuePair<string, int>> with
        member __.GetEnumerator () = featureToIndex.GetEnumerator()
    interface System.Collections.IEnumerable with
        member __.GetEnumerator () = featureToIndex.GetEnumerator() :> _

type [<Sealed>]SparseFeatures(existingFeatures : System.Collections.Generic.IDictionary<string, float>) =
    let backingDictionary = System.Collections.Generic.Dictionary(existingFeatures)
    member private __.GetBackingDictionary = backingDictionary

    new () = SparseFeatures(System.Collections.Generic.Dictionary())
    new (existingFeatures : SparseFeatures) = SparseFeatures(existingFeatures.GetBackingDictionary :> System.Collections.Generic.IDictionary<string, float>)

    interface System.Collections.Generic.IEnumerable<string * float> with
        member __.GetEnumerator () = new Utils.KeyValueAsPairEnumerator<string, float>(backingDictionary.GetEnumerator()) :> _
    interface System.Collections.IEnumerable with
        member __.GetEnumerator () = new Utils.KeyValueAsPairEnumerator<string, float>(backingDictionary.GetEnumerator()) :> _
    interface System.ICloneable with
        member __.Clone () =
            SparseFeatures(backingDictionary) |> box
    override __.ToString () =
        backingDictionary |> Seq.map (fun kv -> System.String.Format("{0}={1:F}", kv.Key, kv.Value)) |> String.concat " "

    member __.Count
        with get () =
            backingDictionary.Count

    member __.Item
        with get key =
            let mutable res = 0.
            if backingDictionary.TryGetValue (key, &res) then
                res
            else
                0.

    member __.Add ((featureName, featureValue) : string * float) =
        if featureValue <> 0. then
            backingDictionary.[featureName] <- featureValue

    member __.AddBool ((featureName, featureValue) : string * bool) =
        if featureValue then
            backingDictionary.[featureName] <- 1.

    member self.AddAll (keyValuePairs : (string * float) seq) =
        Seq.iter self.Add keyValuePairs

    member private self.AddAggregations ((name, expectedCount, featureValues) : (string * int * float list)) =
        let mutable minValue = System.Double.MaxValue
        let mutable maxValue = System.Double.MinValue
        let mutable sum = 0.
        let mutable count = 0
        for featureValue in featureValues do
            minValue <- min minValue featureValue
            maxValue <- max maxValue featureValue
            sum <- sum + featureValue
            count <- count + 1
        self.Add (name + "_avg", sum / (float expectedCount))
        if count < expectedCount then
            self.Add (name + "_min", 0.)
        else
            self.Add (name + "_min", minValue)
        self.Add (name + "_max", maxValue)

    /// Take a list of feature lists, and for each occurring feature name, add the aggregation
    member self.AddFeatureListsAggregated (featuresSeq : #seq<string * float> list) =
        let numberOfSeqs = Seq.length featuresSeq
        let featureGroupMap = ListDictionary()
        for features in featuresSeq do
            Seq.iter featureGroupMap.Add features

        for (name, valueList) in featureGroupMap do
            self.AddAggregations (name, numberOfSeqs, valueList)

    member __.GetFeatureNames () =
        backingDictionary.Keys :> System.Collections.Generic.IEnumerable<string>

    member __.ToFeatureString (featureNameToIndex : FeatureToIndexMap)  =
        backingDictionary
        |> Seq.map (fun kv -> System.String.Format("{0}:{1:F}", featureNameToIndex.GetFeatureId kv.Key, kv.Value))
        |> String.concat "\t"

    member __.ToNamedFeatureStringToWriter (writer : System.IO.TextWriter) =
        for kv in backingDictionary do
            writer.Write(kv.Key)
            writer.Write(':')
            writer.Write(kv.Value)
            writer.Write('\t')

    member __.ToFeatureStringToWriter (featureNameToIndex : FeatureToIndexMap) (writer : System.IO.TextWriter) =
        for kv in backingDictionary do
            writer.Write(featureNameToIndex.GetFeatureId kv.Key)
            writer.Write(':')
            writer.Write(kv.Value)
            writer.Write('\t')

    member __.ToFloatVector (featureNameToIndex : FeatureToIndexMap) =
        let res = Array.zeroCreate<float> featureNameToIndex.Count
        for kv in backingDictionary do
            match featureNameToIndex.GetExistingFeatureId kv.Key with
            | Some id -> res.[id] <- kv.Value
            | None -> () //printfn "Unknown feature %s" kv.Key
        res

    static member ofSeq (keyValuePairs : (string * float) seq) =
        let result = SparseFeatures()
        result.AddAll keyValuePairs
        result

    static member union (features1 : SparseFeatures) (features2 : SparseFeatures) =
        let result = SparseFeatures(features1)
        let resultDict = result.GetBackingDictionary
        for kv in features2.GetBackingDictionary do
            resultDict.Add (kv.Key, kv.Value)
        result

/// Maps value to itself (up to threshold), and to logarithmic bins over that
let private MapValueToNumericBin (threshold : int) (maximalValue : int) (x : int) =
    match x with
    | x when x <= threshold -> x
    | x when x > threshold && x <= maximalValue -> ceil (float(threshold) + log (float(x - threshold + 1))) |> int
    | _ -> ceil (float(threshold) + log (float(maximalValue - threshold))) |> int

/// Extract features concerning the context of a node in a syntax tree (e.g., about parent / sibling nodes, depth, ...)
let ExtractSyntaxTreeFeaturesForNode (st : SyntaxTree.SyntaxTree) (node : SyntaxTree.Node) =
    let NUMBER_OF_PARENTS_TO_CONSIDER = 3

    /// This will hold the list of extracted features:
    let syntaxTreeFeatures = SparseFeatures()

    /////// Extract information about (up to) NUMBER_OF_PARENTS_TO_CONSIDER parents: ///////
    let noParentNode = Node(NULL)
    let mutable curNode = node
    for k in 1 .. NUMBER_OF_PARENTS_TO_CONSIDER do
        let parentNode = defaultArg (st.GetParent curNode) noParentNode
        syntaxTreeFeatures.Add (System.String.Format("c-parent_{0}={1}", k, parentNode.NodeType), 1.)
        curNode <- parentNode

    syntaxTreeFeatures

/// The "depth" of a node in the heap, computed as minimal number of times that the (indegree, outdegree)-information changes on a path from a "root value" (i.e., stack variable)
let private ComputeNodeToUnigramDepth (g : AnnotatedGraph) rootAddresses =
    if Seq.length rootAddresses = 1 then
        g.GetNodeToUnigramDepth (Seq.head rootAddresses)
    else
        let nodeToUnigramDepth = System.Collections.Generic.Dictionary()
        let nodeToUnigramDepthPerAddr = Seq.map g.GetNodeToUnigramDepth rootAddresses
        let allReachableAddrs = System.Collections.Generic.HashSet()
        for depthPerAddr in nodeToUnigramDepthPerAddr do allReachableAddrs.AddAll depthPerAddr.Keys
        for addr in allReachableAddrs do
            nodeToUnigramDepth.[addr] <-
                Seq.min
                    (Seq.map
                        (fun (depthPerAddr : System.Collections.Generic.Dictionary<bigint, int>) -> depthPerAddr.GetWithDefault addr System.Int32.MaxValue)
                        nodeToUnigramDepthPerAddr)

        nodeToUnigramDepth

let private ExtractNgramHeapGraphFeatures (rootAddresses : bigint seq) (g : AnnotatedGraph) forbiddenNodes =
    // specify the numeric ranges of features we are interested in:
    let (thresIndeg, maxIndeg) = (3, 300)
    let (thresOutdeg, maxOutdeg) = (4, 4)
    let (thresDepth, maxDepth) = (5, 20)

    let prefix = match forbiddenNodes with | Some _ -> "exclusive-" | None -> ""
    let nodeToUnigram = g.GetNodeToUnigram ()
    let nodeToUnigramDepth = ComputeNodeToUnigramDepth g rootAddresses

    let occurringNGrams = System.Collections.Generic.HashSet()
    let computeNGramInfoFor addressIndex address =
        let nodesToConsider =
            match forbiddenNodes with
            | None -> g.GetReachable address
            | Some forbiddenNodes -> g.GetReachableWithoutForbidden address forbiddenNodes
        for v in Seq.append [address] nodesToConsider do
            if v <> bigint.Zero then
                let (vInDegree, vOutDegree) = nodeToUnigram.[v]
                let vBinnedInDegree = MapValueToNumericBin thresIndeg maxIndeg vInDegree
                let vBinnedOutDegree = MapValueToNumericBin thresOutdeg maxOutdeg vOutDegree
                let unigram =
                    System.String.Format("{0}unigram:[in={2} out={3} depth={4}]",
                        prefix, addressIndex, vBinnedInDegree, vBinnedOutDegree,
                        (MapValueToNumericBin thresDepth maxDepth nodeToUnigramDepth.[v]))
                occurringNGrams.Add unigram |> ignore

                //Now also compute the bigrams:
                for (_, v') in g.BackingGraph.GetOutEdges v do
                    if v' <> bigint.Zero then
                        let (v'InDegree, v'OutDegree) = nodeToUnigram.[v']
                        let v'BinnedInDegree = MapValueToNumericBin thresIndeg maxIndeg v'InDegree
                        let v'BinnedOutDegree = MapValueToNumericBin thresOutdeg maxOutdeg v'OutDegree
                        let bigram =
                            System.String.Format("{0}bigram:[[inSource={2} outSource={3}] [inTarget={4} outTarget={5}]]",
                                prefix, addressIndex,
                                vBinnedInDegree, vBinnedOutDegree,
                                v'BinnedInDegree, v'BinnedOutDegree)
                        occurringNGrams.Add bigram |> ignore
    rootAddresses |> Seq.iteri computeNGramInfoFor
    occurringNGrams |> Seq.map (fun ng -> ng, 1.) |> Seq.toList |> Seq.cache

let private AddressIsCyclic (heapGraph : AnnotatedGraph) =
    heapGraph.IsInSCC
let private AddressReachesCycle (heapGraph: AnnotatedGraph) addr =
    heapGraph.SomeInSCC (heapGraph.GetReachable addr)
let private AddressesShare (heapGraph : AnnotatedGraph) addr1 addr2 =
    (heapGraph.GetReachable addr1).Overlaps (heapGraph.GetReachable addr2)

let private AddressReachesAddress (heapGraph : AnnotatedGraph) addr1 addr2 =
    (heapGraph.GetReachable addr1).Contains addr2
let private AddressReachesAddressOnNonDataEdgesWithoutPassingOther (heapGraph : AnnotatedGraph) addr1 addr2 otherAddresses =
    let dataLabels = Utils.KnownDataFieldIds
    heapGraph.IsReachableWithoutForbidden addr1 addr2 otherAddresses dataLabels
let private AddressReachesAddressWithOneLabel (heapGraph : AnnotatedGraph) addr1 addr2 =
    heapGraph.IsReachableViaOneLabel addr1 addr2
// Reflexive versions of the above:
let private AddressReachesAddressReflx (heapGraph : AnnotatedGraph) addr1 addr2 =
    addr1 = addr2 || (heapGraph.GetReachable addr1).Contains addr2
let private AddressReachesAddressOnNonDataEdgesWithoutPassingOtherReflx (heapGraph : AnnotatedGraph) addr1 addr2 otherAddresses =
    let dataLabels = Utils.KnownDataFieldIds
    addr1 = addr2 || heapGraph.IsReachableWithoutForbidden addr1 addr2 otherAddresses dataLabels
let private AddressReachesAddressWithOneLabelReflx (heapGraph : AnnotatedGraph) addr1 addr2 =
    addr1 = addr2 || heapGraph.IsReachableViaOneLabel addr1 addr2


let GetReachabilityFeatures varList (env: Environment) =
    let hGraph, vEnv = env
    let varAddrList = List.map (fun v -> v, (Map.find (SepLogic.VarAddr v) vEnv).GetValAddr()) varList
    [|for _, uAddr in varAddrList do
        for _, vAddr in varAddrList do
            let otherAddrs = List.filter (fun (_, a) -> a <> uAddr && a <> vAddr) varAddrList |> List.map snd

            // One feature to rule them all
            if uAddr = vAddr then
                yield 1.0  // Equal
            elif AddressReachesAddressOnNonDataEdgesWithoutPassingOtherReflx hGraph.Graph uAddr vAddr otherAddrs then
                yield 0.9  // Can reach without passing other vars
            elif AddressReachesAddress hGraph.Graph uAddr vAddr then
                yield 0.4  // Can reach by passing others
            else
                yield 0.0  // Can't reach
    |]


/// interface for heap graph feature extraction -- reports back a sparse vector, only listing non-0 features
let ExtractHeapGraphFeatures (environments : Environment list) : SparseFeatures =
    let mutable combinedFeatures = []
    for (heapGraph, varEnv) in environments do
        let allVars = Value.valSeqToAddrSeq varEnv.Values
        let features = ExtractNgramHeapGraphFeatures allVars heapGraph.Graph None
        combinedFeatures <- features :: combinedFeatures
    let features = SparseFeatures()
    features.AddFeatureListsAggregated combinedFeatures
    features

let AddressesToExistentialsDataSet (heapGraph : AnnotatedGraph) (rootAddresses : bigint seq) (namedAddresses : bigint seq) =
    let addresses = System.Collections.Generic.HashSet()
    let addressesWithoutForbidden = System.Collections.Generic.HashSet()
    for rootAddress in rootAddresses do
        addresses.AddAll (heapGraph.GetReachable rootAddress)
        addressesWithoutForbidden.AddAll (heapGraph.GetReachableWithoutForbidden rootAddress namedAddresses)
    let namedAddresses = System.Collections.Generic.HashSet(namedAddresses)
    let unigramInfo = heapGraph.GetNodeToUnigram()
    let unigramDepth = ComputeNodeToUnigramDepth heapGraph rootAddresses

    let sumInDegreePerDepth = System.Collections.Generic.Dictionary()
    let sumOutDegreePerDepth = System.Collections.Generic.Dictionary()
    let nodeCountPerDepth = System.Collections.Generic.Dictionary()
    addresses.Remove bigint.Zero |> ignore
    for address in addresses do
        let (addrInDegree, addrOutDegree) = unigramInfo.[address]
        let addrDepth = unigramDepth.[address]
        match nodeCountPerDepth.TryGetValue addrDepth with
        | (true, c)  ->
            nodeCountPerDepth.[addrDepth] <- c + 1
            sumInDegreePerDepth.[addrDepth] <- sumInDegreePerDepth.[addrDepth] + addrInDegree
            sumOutDegreePerDepth.[addrDepth] <- sumOutDegreePerDepth.[addrDepth] + addrOutDegree
        | (false, _) ->
            nodeCountPerDepth.[addrDepth] <- 1
            sumInDegreePerDepth.[addrDepth] <- addrInDegree
            sumOutDegreePerDepth.[addrDepth] <- addrOutDegree
    let avgInDegreePerDepth = System.Collections.Generic.Dictionary()
    let avgOutDegreePerDepth = System.Collections.Generic.Dictionary()
    for KeyValue(depth, nodeCount) in nodeCountPerDepth do
        avgInDegreePerDepth.[depth] <- float sumInDegreePerDepth.[depth] / float nodeCount
        avgOutDegreePerDepth.[depth] <- float sumOutDegreePerDepth.[depth] / float nodeCount

    [
        for addr in addresses do
            let addressFeatures = SparseFeatures()

            addressFeatures.AddBool ("addr_is_cyclic", AddressIsCyclic heapGraph addr)
            addressFeatures.AddBool ("addr_reaches_cycle", AddressReachesCycle heapGraph addr)
            addressFeatures.AddAll (ExtractNgramHeapGraphFeatures [addr] heapGraph None)
            addressFeatures.AddBool ("named", namedAddresses.Contains addr)
            addressFeatures.AddBool ("reachableWithoutForbidden", addressesWithoutForbidden.Contains addr)
            let (inDeg, outDeg) = unigramInfo.[addr]
            let depth = unigramDepth.[addr]
            addressFeatures.AddBool ("inDeg=" + string inDeg, true)
            addressFeatures.AddBool ("outDeg=" + string outDeg, true)
            let binnedUnigramDepth = MapValueToNumericBin 2 4 depth
            addressFeatures.AddBool ("depth=" + string binnedUnigramDepth, true)
            addressFeatures.AddBool ("inDegAboveAverageAtDepth", float inDeg > avgInDegreePerDepth.[depth])
            addressFeatures.AddBool ("inDegBelowAverageAtDepth", float inDeg < avgInDegreePerDepth.[depth])
            addressFeatures.AddBool ("outDegAboveAverageAtDepth", float outDeg > avgOutDegreePerDepth.[depth])
            addressFeatures.AddBool ("outDegBelowAverageAtDepth", float outDeg < avgOutDegreePerDepth.[depth])

            let incomingEdgeLabels = heapGraph.BackingGraph.GetInEdges addr |> Seq.map snd |> Set.ofSeq
            let outgoingEdgeLabels = heapGraph.BackingGraph.GetOutEdges addr |> Seq.map fst |> Set.ofSeq
            addressFeatures.AddBool ("numberOfDifferentIncomingEdgeLabels=" + string incomingEdgeLabels.Count, true)
            addressFeatures.AddBool ("incomingEdgeLabelsSubsetOfOutgoing", Set.isSubset incomingEdgeLabels outgoingEdgeLabels)
            addressFeatures.AddBool ("incomingEdgeLabelsProperSubsetOfOutgoing", Set.isProperSubset incomingEdgeLabels outgoingEdgeLabels)
            addressFeatures.AddBool ("outgoingEdgeLabelsSubsetOfIncoming", Set.isSubset outgoingEdgeLabels incomingEdgeLabels)
            addressFeatures.AddBool ("outgoingEdgeLabelsProperSubsetOfIncoming", Set.isProperSubset outgoingEdgeLabels incomingEdgeLabels)

            let predecessorsAtSameDepth =
                heapGraph.BackingGraph.GetInEdges addr
                |> Set.filter (fun (w, _) -> addresses.Contains w && unigramDepth.[w] = depth)
            let (cyclicPredecessorsAtSameDepth, acyclicPredecessorsAtSameDepth) =
                predecessorsAtSameDepth
                |> Set.fold (fun (cyclic, acyclic) (w, _) -> if AddressIsCyclic heapGraph w then (cyclic + 1, acyclic) else (cyclic, acyclic + 1)) (0, 0)
            let successorsAtSameDepth =
                heapGraph.BackingGraph.GetOutEdges addr
                |> Set.filter (fun (_, w) -> w <> bigint.Zero && addresses.Contains w && unigramDepth.[w] = depth)
            let (cyclicSuccessorsAtSameDepth, acyclicSuccessorsAtSameDepth) =
                successorsAtSameDepth
                |> Set.fold (fun (cyclic, acyclic) (_, w) -> if AddressIsCyclic heapGraph w then (cyclic + 1, acyclic) else (cyclic, acyclic + 1)) (0, 0)
            addressFeatures.AddBool ("allPredecessorsAtSameDepthCyclic", 0 = acyclicPredecessorsAtSameDepth)
            addressFeatures.AddBool ("allPredecessorsAtSameDepthAcyclic", 0 = cyclicPredecessorsAtSameDepth)
            addressFeatures.AddBool ("allSuccessorsAtSameDepthCyclic", 0 = acyclicSuccessorsAtSameDepth)
            addressFeatures.AddBool ("allSuccessorsAtSameDepthAcyclic", 0 = cyclicSuccessorsAtSameDepth)

            yield (addr, addressFeatures)
    ]

/// Compute the subheaps induced by nested symbolic heaps in a predicate, under the assumption that the given predicate describes the data structure and has arguments initialAddresses
/// Subheaps are returned as a "root" address, and are understood as the subgraph of the heap reachable from these root addresses.
/// Extraction is stopped whenever another named address is found, where we assume that another subheap starts
let GetSubHeapsOfPredicate (heapGraph : AnnotatedGraph) (definedPredicate : SepLogic.PredicateName) (initialAddresses : bigint seq) (otherNamedAddresses : bigint seq) =
    //For example for lists, we want to follow the "1" pointer, and the subheap is whatever is reachable from the "0" pointer.
    let mutable res = []
    let definedAddress = Seq.head initialAddresses
    let mutable stack = [definedAddress]
    let seen = System.Collections.Generic.HashSet()
    let otherNamedAddresses = System.Collections.Generic.HashSet(otherNamedAddresses)
    while not (List.isEmpty stack) do
        let curAddress = List.head stack
        stack <- List.tail stack

        if seen.Add curAddress && not (otherNamedAddresses.Contains curAddress) then
            let outEdges = heapGraph.BackingGraph.GetOutEdges curAddress
            if outEdges.Count > 0 then
                let (valueEdges, recursiveEdges) = Seq.partition (fst >> HeapLabel.IsDataField) outEdges
                // If the "data" field is not Addr type, then there are no subheaps:
                if not valueEdges.IsEmpty then
                    match definedPredicate with
                    | SepLogic.List ->
                        // Get instantiations of arguments of nested data structures (free1, free2, ex1, ex2) = (current, end of list, value, next)
                        let subheapStart = List.map snd valueEdges |> List.head
                        let nestedArguments = curAddress :: (Seq.last initialAddresses) :: subheapStart :: (List.map snd recursiveEdges)
                        res <- (Seq.singleton subheapStart, nestedArguments) :: res
                        stack <- (List.map snd recursiveEdges) @ stack
                    | SepLogic.Tree ->
                        // Get instantiations of arguments of nested data structures (free1, ex1, ex2, ex3) = (current, value, left, right)
                        let subheapStart = List.map snd valueEdges |> List.head
                        let nestedArguments = curAddress :: subheapStart :: (recursiveEdges |> List.sortBy fst |> List.map snd)
                        res <- (Seq.singleton subheapStart, nestedArguments) :: res
                        stack <- (List.map snd recursiveEdges) @ stack
    res

let inline GetVariableValue (varEnvironment : VarEnvironment) var =
    match Map.tryFind var varEnvironment with
    | None -> failwith (sprintf "Environment %s doesn't have variable %s" (varEnvironment.ToString ()) (var.Name))
    | Some v -> v

let inline GetAddrOfVar (varEnvironment : VarEnvironment) var =
    match GetVariableValue varEnvironment var with
    | Value.ValAddr addr -> addr
    | v -> failwith (sprintf "GetAddrOfVar called on var %s with non Addr value %s" var.Name (v.ToString ()))

let inline GetAddrOfVarName (varEnvironment : VarEnvironment) varName =
    if varName = "nil" then
        bigint.Zero
    else
        GetAddrOfVar varEnvironment (SepLogic.VarAddr varName)

let private ComputeNewEnvironments (environments : Environment list) (syntaxTree : SyntaxTree.SyntaxTree) curNode heapletType existentialsFeatures =
    // Find the nested predicate:
    let children = syntaxTree.GetChildren curNode
    let nestedLambdaNode = Seq.find (fun (childNode : SyntaxTree.Node) -> childNode.NodeType = LambdaBinding) children
    let nestedLambdaChildNode = Seq.head (syntaxTree.GetChildren nestedLambdaNode)
    match nestedLambdaChildNode.NodeType with
    | TypedLambdaBinding _ -> //We have substructures, in a structure of type heapletType. Find out where it begins, and enumerate subheaps:
        let typedHeapletArguments = syntaxTree.GetTypedHeapletArguments curNode
        let argumentVarNames = Seq.map (syntaxTree.GetNameFromExpressionNode) typedHeapletArguments

        //Identify existentials in our lambda binding:
        let nestedSymHeap = syntaxTree.GetChildren nestedLambdaChildNode |> Seq.find (fun (n : SyntaxTree.Node) -> n.NodeType = Symheap)

        let lambdaBoundVariables =
            syntaxTree.GetChildren nestedLambdaChildNode
            |> Seq.filter (fun (n : SyntaxTree.Node) -> n.NodeType.IsVar)
            |> Seq.map (fun n -> SepLogic.VarAddr (syntaxTree.GetNameFromExpressionNode n))
            |> List.ofSeq

        let mutable existentiallyQuantifiedVariables = []
        let mutable tNode = syntaxTree.GetChildren nestedSymHeap |> Seq.tryFind (fun (n : SyntaxTree.Node) -> n.NodeType = ExistentialBinding)
        while tNode.IsSome do
            existentiallyQuantifiedVariables <-
                  (syntaxTree.GetChildren tNode.Value
                |> Seq.find (fun (n : SyntaxTree.Node) -> n.NodeType.IsVar)
                |> (fun n -> SepLogic.VarAddr (syntaxTree.GetNameFromExpressionNode n))) :: existentiallyQuantifiedVariables
            tNode <- syntaxTree.GetChildren tNode.Value |> Seq.tryFind (fun (n : SyntaxTree.Node) -> n.NodeType = ExistentialBinding) 

        let workaround() = null |> ignore // c.f. https://github.com/Microsoft/visualfsharp/issues/759

        let mutable newEnvironments = []
        for (heapGraph, oldVarEnvironment) as oldEnvironment in environments do
            let argumentVarAddrs = Seq.map (GetAddrOfVarName oldVarEnvironment) argumentVarNames
            let definedVar = Seq.head argumentVarNames
            let otherNamedAddresses =
                oldVarEnvironment
                |> Seq.filter (fun t -> match t.Key with | SepLogic.VarAddr n | SepLogic.VarInt n -> n <> definedVar)
                |> Seq.map (fun t -> t.Value)
                |> Value.valSeqToAddrSeq
            for (subheapStarts, nestedArguments) in GetSubHeapsOfPredicate heapGraph.Graph heapletType argumentVarAddrs otherNamedAddresses do
                workaround() // c.f. https://github.com/Microsoft/visualfsharp/issues/759
                for subheapStart in subheapStarts do
                    if subheapStart <> bigint.Zero then
                        //Step 1: Note this subheap in our result
                        let mutable namedAddresses = nestedArguments @ (oldVarEnvironment.Values |> Value.valSeqToAddrSeq |> List.ofSeq)
                        let existentialAddresses = heapGraph.SubheapStartsToExistentials.[subheapStart]
                        for existentialAddress in existentialAddresses do
                            existentialsFeatures := 
                                (AddressesToExistentialsDataSet heapGraph.Graph [subheapStart] namedAddresses
                                 |> List.map (fun (addr, feat) -> (existentialAddress = addr, addr, feat)))
                                :: !existentialsFeatures
                            namedAddresses <- existentialAddress :: namedAddresses
                        //And now one for the "no more" case:
                        existentialsFeatures := 
                            (AddressesToExistentialsDataSet heapGraph.Graph [subheapStart] namedAddresses
                             |> List.map (fun (addr, feat) -> (false, addr, feat)))
                            :: !existentialsFeatures

                        //Step 2: Recursion: For that, set variables to the right values:
                        // first lambda-bound variables to arguments of predicate and existentials of the rule,
                        // second part to existentials bound in subheap (get from map from state generation)
                        let lambdaBindings = List.zip lambdaBoundVariables (Value.addrSeqToValSeq nestedArguments |> List.ofSeq)
                        let existentialsBindings = Seq.zip existentiallyQuantifiedVariables (Value.addrSeqToValSeq existentialAddresses)
                        let extendedVarEnvironment = Map.addMany (Map.addMany oldVarEnvironment lambdaBindings) existentialsBindings
                        newEnvironments <- (oldEnvironment, Seq.singleton subheapStart, (heapGraph, extendedVarEnvironment)) :: newEnvironments
        Some (nestedSymHeap, newEnvironments)
    | _ -> None //NoLambda, so nothing to do

let private GetFeaturesForVariable ((heapGraph, varEnvironment) : Environment) (isInDefiningPosition : bool) (enclosingVariables : SepLogic.VarName seq) (variable : SepLogic.VarName) (variablesToSyntacticallyReachableVariables : SetDictionary<SepLogic.VarName, SepLogic.VarName>) variableAddr =
    [
        if variableAddr = bigint.Zero then //Do not consider null case
            yield ("value_is_nil", 1.0)
        
        yield ("addr_is_cyclic", AddressIsCyclic heapGraph.Graph variableAddr |> Bool2Float)
        yield ("addr_reaches_cycle", AddressReachesCycle heapGraph.Graph variableAddr |> Bool2Float)
        if isInDefiningPosition then
            let otherAddresses = varEnvironment.Items |> Seq.collect (fun (_ , addr) -> if addr <> Value.ValAddr variableAddr then [addr] else [])
                                                      |> Value.valSeqToAddrSeq
            yield! ExtractNgramHeapGraphFeatures [variableAddr] heapGraph.Graph (Some otherAddresses) 

        //Compute relation of this variable to the enclosing defined variables:
        for (idx, enclosingVariable) in Seq.mapi (fun i v -> (i, v)) enclosingVariables do
            let enclosingVariableAddr = GetAddrOfVarName varEnvironment enclosingVariable
            // if variableAddr <> bigint.Zero then
            let otherAddrs = System.Collections.Generic.HashSet()
            for (var, value) in varEnvironment.Items do
                match value with
                | State.ValAddr addr ->
                    if enclosingVariable <> var.Name && variableAddr <> addr then
                        otherAddrs.Add addr |> ignore
                | _ -> ()

            yield (System.String.Format("reaches_{0}th_enclosing_addr", idx),
                    AddressReachesAddress heapGraph.Graph variableAddr enclosingVariableAddr |> Bool2Float)
            yield (System.String.Format("reaches_via_nondata_{0}th_enclosing_addr_without_passing_other_var", idx),
                    AddressReachesAddressOnNonDataEdgesWithoutPassingOther heapGraph.Graph variableAddr enclosingVariableAddr otherAddrs |> Bool2Float)
            yield (System.String.Format("reaches_{0}th_enclosing_addr_with_one_label", idx),
                    AddressReachesAddressWithOneLabel heapGraph.Graph variableAddr enclosingVariableAddr |> Bool2Float)
            yield (System.String.Format("reached_from_{0}th_enclosing_addr", idx),
                    AddressReachesAddress heapGraph.Graph enclosingVariableAddr variableAddr |> Bool2Float)
            yield (System.String.Format("reached_via_nondata_from_{0}th_enclosing_addr_without_passing_other_var", idx),
                    AddressReachesAddressOnNonDataEdgesWithoutPassingOther heapGraph.Graph enclosingVariableAddr variableAddr otherAddrs |> Bool2Float)
            yield (System.String.Format("reached_from_{0}th_enclosing_addr_with_one_label", idx),
                    AddressReachesAddressWithOneLabel heapGraph.Graph enclosingVariableAddr variableAddr |> Bool2Float)
            // Also add reflexive versions of these:
            yield (System.String.Format("reflx_reaches_{0}th_enclosing_addr", idx),
                    AddressReachesAddressReflx heapGraph.Graph variableAddr enclosingVariableAddr |> Bool2Float)
            yield (System.String.Format("reflx_reaches_via_nondata_{0}th_enclosing_addr_without_passing_other_var", idx),
                    AddressReachesAddressOnNonDataEdgesWithoutPassingOtherReflx heapGraph.Graph variableAddr enclosingVariableAddr otherAddrs |> Bool2Float)
            yield (System.String.Format("reflx_reaches_{0}th_enclosing_addr_with_one_label", idx),
                    AddressReachesAddressWithOneLabelReflx heapGraph.Graph variableAddr enclosingVariableAddr |> Bool2Float)
            yield (System.String.Format("reflx_reached_from_{0}th_enclosing_addr", idx),
                    AddressReachesAddressReflx heapGraph.Graph enclosingVariableAddr variableAddr |> Bool2Float)
            yield (System.String.Format("reflx_reached_via_nondata_from_{0}th_enclosing_addr_without_passing_other_var", idx),
                    AddressReachesAddressOnNonDataEdgesWithoutPassingOtherReflx heapGraph.Graph enclosingVariableAddr variableAddr otherAddrs |> Bool2Float)
            yield (System.String.Format("reflx_reached_from_{0}th_enclosing_addr_with_one_label", idx),
                    AddressReachesAddressWithOneLabelReflx heapGraph.Graph enclosingVariableAddr variableAddr |> Bool2Float)

            yield (System.String.Format("shares_with_{0}th_enclosing_addr", idx),
                    AddressesShare heapGraph.Graph variableAddr enclosingVariableAddr |> Bool2Float)
            yield (System.String.Format("equal_to_{0}th_enclosing_addr", idx),
                (=) variableAddr enclosingVariableAddr |> Bool2Float)

            yield (System.String.Format("syntactically_reaches_{0}th_enclosing_addr", idx),
                    variablesToSyntacticallyReachableVariables.[variable].Contains enclosingVariable |> Bool2Float)
            yield (System.String.Format("syntactically_reached_from_{0}th_enclosing_addr", idx),
                    variablesToSyntacticallyReachableVariables.[enclosingVariable].Contains variable |> Bool2Float)
            yield (System.String.Format("{0}th_enclosing_addr_is_cyclic", idx),
                   AddressIsCyclic heapGraph.Graph enclosingVariableAddr |> Bool2Float)
    ]

let private GetFeaturesForNilExpression ((heapGraph, varEnvironment) : Environment) (enclosingVariables : SepLogic.VarName seq) =
    [
        yield ("value_is_nil", true |> Bool2Float)

        //Compute relation of nil to the enclosing defined variables:
        for (idx, enclosingVariable) in Seq.mapi (fun i v -> (i, v)) enclosingVariables do
            let enclosingVariableAddr = GetAddrOfVarName varEnvironment enclosingVariable
            let otherAddrs = System.Collections.Generic.HashSet()
            for (var, value) in varEnvironment.Items do
                match value with
                | State.ValAddr addr ->
                    if enclosingVariable <> var.Name then
                        otherAddrs.Add addr |> ignore
                | _ -> ()


            yield (System.String.Format("reached_from_{0}th_enclosing_addr", idx),
                   AddressReachesAddress heapGraph.Graph enclosingVariableAddr bigint.Zero |> Bool2Float)
            yield (System.String.Format("reached_via_nondata_from_{0}th_enclosing_addr_without_passing_other_var", idx),
                   AddressReachesAddressOnNonDataEdgesWithoutPassingOther heapGraph.Graph enclosingVariableAddr bigint.Zero otherAddrs |> Bool2Float)
            yield (System.String.Format("reached_from_{0}th_enclosing_addr_with_one_label", idx),
                    AddressReachesAddressWithOneLabel heapGraph.Graph enclosingVariableAddr bigint.Zero |> Bool2Float)
            // And the reflexive versions:
            yield (System.String.Format("reflx_reached_from_{0}th_enclosing_addr", idx),
                   AddressReachesAddressReflx heapGraph.Graph enclosingVariableAddr bigint.Zero |> Bool2Float)
            yield (System.String.Format("reflx_reached_via_nondata_from_{0}th_enclosing_addr_without_passing_other_var", idx),
                   AddressReachesAddressOnNonDataEdgesWithoutPassingOtherReflx heapGraph.Graph enclosingVariableAddr bigint.Zero otherAddrs |> Bool2Float)
            yield (System.String.Format("reflx_reached_from_{0}th_enclosing_addr_with_one_label", idx),
                    AddressReachesAddressWithOneLabelReflx heapGraph.Graph enclosingVariableAddr bigint.Zero |> Bool2Float)

            yield (System.String.Format("{0}th_enclosing_addr_is_cyclic", idx),
                   AddressIsCyclic heapGraph.Graph enclosingVariableAddr |> Bool2Float)
    ]

let private GetFeaturesForExpressionCandidates ((_, varEnvironment) as environment : Environment) (isInDefiningPosition : bool) (variableCandidates : SepLogic.VarName seq) (enclosingVariables : SepLogic.VarName seq) (variablesToSyntacticallyReachableVariables : SetDictionary<SepLogic.VarName, SepLogic.VarName>) =
    let mutable res = [ ("nil", GetFeaturesForNilExpression environment enclosingVariables) ]
    for variable in variableCandidates do
        let variableAddr = 
            match varEnvironment.[SepLogic.VarAddr variable] with
            | Value.ValAddr addr -> addr
            | v -> failwith (sprintf "Addr variable %s with non Addr value %s" variable (v.ToString ()))
        res <- (variable, GetFeaturesForVariable environment isInDefiningPosition enclosingVariables variable variablesToSyntacticallyReachableVariables variableAddr) :: res
    res

let ComputeExpressionFeatures stackVariables (environments : Environment list) (syntaxTree : SyntaxTree.SyntaxTree) (expressionNode : SyntaxTree.Node) (chosenExpression : Program.VarName) =
    let enclosingDefinedVariables = syntaxTree.GetEnclosingDefinedVariableNodes expressionNode |> Seq.map (fun n -> n.GetNameFromExpressionId)
    
    let variablesToSyntacticallyReachableVariables = syntaxTree.GetDefinedToReachableVariables expressionNode

    let exprNodeIsInDefiningPosition = 
        expressionNode = (syntaxTree.GetChildren (syntaxTree.GetParent expressionNode).Value |> Seq.filter (fun n -> n.NodeType.IsExpr) |> Seq.head)

    let (isInInner, definableVariables) = syntaxTree.GetDefinableVariablesInScope expressionNode
    let definableVariables =
        if definableVariables.IsEmpty || not exprNodeIsInDefiningPosition then // Nothing specific in scope, so allow everything
            match environments with
            | (_, vEnv) :: _ -> vEnv.Keys |> Seq.map (fun v -> v.Name)
            | _ -> Seq.empty
        else
            if isInInner then
                definableVariables :> _
            else
                Seq.append stackVariables definableVariables

    let variableToFeaturesSeq = ListDictionary()
    let alreadyDefinedVariables = syntaxTree.GetAlreadyDefinedVariables expressionNode |> Set.ofList
    let somewhereUndefVariables = System.Collections.Generic.HashSet()
    if not environments.IsEmpty then
        for (_, vEnv) as env in environments do
            for (expr, features) in GetFeaturesForExpressionCandidates env exprNodeIsInDefiningPosition definableVariables enclosingDefinedVariables variablesToSyntacticallyReachableVariables do
                variableToFeaturesSeq.Add (expr, features)
                let exprVal = vEnv.TryFind (SepLogic.VarAddr expr)
                if expr <> "nil" && exprVal <> None && exprVal.Value <> Value.ValAddr bigint.Zero then
                    let isUndefSomewhere =
                        alreadyDefinedVariables
                        |> Set.forall (fun defVar -> exprVal <> vEnv.TryFind (SepLogic.VarAddr defVar))
                    if isUndefSomewhere then
                        somewhereUndefVariables.Add expr |> ignore


    let sortedUndefVars = somewhereUndefVariables |> List.ofSeq |> List.sort
    let undefVarsNum = List.length sortedUndefVars
    let mutable thisExprFeatures = []
    for (variable, featuresSeq) in variableToFeaturesSeq do
        let features = SparseFeatures()
        features.AddFeatureListsAggregated featuresSeq

        features.AddBool ("expr_is_nil", false)
        if exprNodeIsInDefiningPosition then
            features.AddBool ("already_defined", Set.contains variable alreadyDefinedVariables)
            features.Add ("remaining_undef_nonnil_var", float (undefVarsNum - (defaultArg (List.tryFindIndex ((=) variable) sortedUndefVars) undefVarsNum)))

        thisExprFeatures <- (chosenExpression = variable, variable, features) :: thisExprFeatures
    thisExprFeatures

let ComputeLambdaFeatures
        (oldEnvironmentsWithSubheapStarts : (Environment * bigint seq) list)
        (syntaxTree : SyntaxTree)
        (lambdaNode : Node) =
    let subheapFeatures =
        if oldEnvironmentsWithSubheapStarts = [] then
            [ Seq.singleton ("empty_subheap", 1.) ]
        else
            oldEnvironmentsWithSubheapStarts
            |> List.map
                (fun ((heapGraph, oldVarEnv), subheapStart) ->
                    if not(Seq.isEmpty subheapStart) && (Seq.head subheapStart) <> bigint.Zero then
                        let ngramInfo = ExtractNgramHeapGraphFeatures subheapStart heapGraph.Graph (Some (Value.valSeqToAddrSeq oldVarEnv.Values))
                        //MOAR?
                        Seq.append [("has_subheap", 1.)] ngramInfo
                    else
                        Seq.singleton ("empty_subheap", 1.))
    let lambdaFeatures = ExtractSyntaxTreeFeaturesForNode syntaxTree lambdaNode
    lambdaFeatures.AddFeatureListsAggregated subheapFeatures
    lambdaFeatures

let ComputeHeapletFeatures
        (environments : Environment list)
        (stackVariables : SepLogic.VarName seq)
        (syntaxTree : SyntaxTree)
        (node : Node) =
    /// We compute features for those parts of the heap that haven't been
    /// "explained" yet, by looking at declared variables that haven't been
    /// defined (yet). We just pick the first one.

    // Compute the variables that COULD be defined (i.e., stack variables,
    // things bound in existentials, things in definable positions in nested
    // lambdas)
    let (isInInner, definableVariables) = syntaxTree.GetDefinableVariablesInScope node
    let definableVariables =
        if definableVariables.IsEmpty then // Nothing specific in scope, so allow everything
            stackVariables
        else
            if isInInner then
                definableVariables :> _
            else
                Seq.append stackVariables definableVariables
    let definableVariables = Set.ofSeq definableVariables

    // Compute the variables that are already defined. We use that all
    // environments are defined on the same keys.
    let definedVariables = syntaxTree.GetAlreadyDefinedVariables node |> Set.ofList
    let undefinedVariables = Set.removeAll definedVariables definableVariables |> Array.ofSeq

    // Compute which of those are non-nil in at least one heap:
    let variableIsNonNil = Array.create undefinedVariables.Length false
    for (_, varEnv) in environments do
        for varIdx in 0 .. undefinedVariables.Length - 1 do
            let var = undefinedVariables.[varIdx]
            variableIsNonNil.[varIdx] <- 
                variableIsNonNil.[varIdx] || GetAddrOfVarName varEnv var <> bigint.Zero

    let undefinedNonNilVariables =
        [ for (var, isNonNil) in Array.zip undefinedVariables variableIsNonNil do
            if isNonNil then yield var ]

    // Now take the first undefined variable whose value is non-nil and
    // extract features, if there is one:
    let syntaxTreeFeatures = SparseFeatures()
    if not (List.isEmpty undefinedNonNilVariables) then
        let undefinedPartsFeatures =
            [
                for (heapGraph, varEnv) in environments do
                    let undefinedVarAddrs = undefinedNonNilVariables |> List.map (GetAddrOfVarName varEnv)
                    let nGramFeatures = ExtractNgramHeapGraphFeatures undefinedVarAddrs heapGraph.Graph None
                    yield nGramFeatures
            ] 
        syntaxTreeFeatures.AddFeatureListsAggregated undefinedPartsFeatures
    syntaxTreeFeatures

let ComputeHeapletsFeatures
        (environments : Environment list)
        (stackVariables : SepLogic.VarName seq)
        (syntaxTree : SyntaxTree)
        (node : Node) =
    let nodeFeatures = SparseFeatures()

    // Compute the variables that COULD be defined (i.e., stack variables, things bound in existentials, things in definable positions in nested lambdas)
    let (isInInner, definableVariables) = syntaxTree.GetDefinableVariablesInScope node
    let definableVariables =
        if definableVariables.IsEmpty then // Nothing specific in scope, so allow everything
            stackVariables
        else
            if isInInner then
                definableVariables :> _
            else
                Seq.append stackVariables definableVariables
    let definableVariables = Set.ofSeq definableVariables
    let definedVariables = syntaxTree.GetAlreadyDefinedVariables node |> Set.ofList
    let undefinedVariables = Set.removeAll definedVariables definableVariables

    let heapletsHeapFeatures =
        environments
        |> List.map
            (fun (heapGraph, varEnv) ->
                //Compute if there is anything reachable that we haven't covered so far.
                let alreadyDefinedAddresses =
                    definedVariables
                    |> Set.map (GetAddrOfVarName varEnv)
                let definableAddresses =
                    definableVariables
                    |> Set.map (GetAddrOfVarName varEnv)
                    |> Set.removeAll alreadyDefinedAddresses

                let undefinedNonNilVariables =
                    undefinedVariables
                    |> Set.filter (fun varName -> bigint.Zero <> GetAddrOfVarName varEnv varName
                                                  && not (alreadyDefinedAddresses.Contains (GetAddrOfVarName varEnv varName)))
                let undefinedVariablesFeature = [("num-undefined-nonnil-variables", float undefinedNonNilVariables.Count)]

                let allReachable = System.Collections.Generic.HashSet()
                for address in definableAddresses do
                    if address <> bigint.Zero then
                        allReachable.AddAll (heapGraph.Graph.GetReachableWithoutForbidden address alreadyDefinedAddresses)

                if allReachable.Count > 0 then
                    ("num-undefined-reachable-addrs", float allReachable.Count) :: undefinedVariablesFeature
                else
                    ("has-no-undefined-reachable-addrs", 1.0) :: undefinedVariablesFeature)

    nodeFeatures.AddFeatureListsAggregated heapletsHeapFeatures
    nodeFeatures

let ComputeProductionFeaturesFromSyntaxTree
        (envsWithExVarInformation : (Environment * Map<SepLogic.TypedVar, Value>) list)
        (syntaxTree : SyntaxTree.SyntaxTree) =
    //these three will hold the results:
    let nodeTypeToFeatureAndProductionPairs = ListDictionary()
    let exprFeatureGroups = ListDictionary()
    let existentialsFeatures = ref []
   
    let mutable environments = []
    for ((heapGraph, varEnv), exVarsToAddr) in envsWithExVarInformation do
        let stackAddresses = varEnv.Values |> Value.valSeqToAddrSeq |> List.ofSeq
        let mutable namedAddresses = stackAddresses
        for exAddr in exVarsToAddr.Values |> Value.valSeqToAddrSeq do
            existentialsFeatures :=
                (AddressesToExistentialsDataSet heapGraph.Graph stackAddresses namedAddresses
                 |> List.map (fun (addr, feat) -> (exAddr = addr, addr, feat)))
                :: !existentialsFeatures
            namedAddresses <- exAddr :: namedAddresses
        existentialsFeatures :=
            (AddressesToExistentialsDataSet heapGraph.Graph stackAddresses namedAddresses
             |> List.map (fun (addr, feat) -> (false, addr, feat)))
            :: !existentialsFeatures
        let varEnv = Map.union varEnv exVarsToAddr
        environments <- (heapGraph, varEnv) :: environments

    let usedVarNames = Seq.map (fun (v : SepLogic.TypedVar) -> v.Name) (List.head environments |> (fun (_, varEnv) -> varEnv.Keys))
    let heapFeatures = ExtractHeapGraphFeatures environments

    let inline getChosenProduction node =
        STProduction(System.Collections.Generic.List(syntaxTree.GetChildren node |> Seq.map (fun n -> n.NodeType)))

    /// Recurses through the syntax tree, and instantiates variables bound in
    /// existential quantification / lambda expressions appropriately.
    /// At each node, notes the used production and the features computed in
    /// context.
    /// Special cases:
    ///  - TypedHeaplet nodes, which handles a number of things in one go.
    ///    We directly look at the nested lambda expression and enumerate 
    ///    variable instantiations based on our assumptions about the data
    ///    structure so far.
    ///    In the course of that, we also handle the case of a nested
    ///    existential binding, by storing a list of (isExQuantified, addr, 
    ///    features) pairs for each address.
    ///  - Expression nodes, where we extract features for all declared
    ///    variables + nil, and store a list of (isRightExpression, expr, 
    ///    features) pairs.
    let rec visitSyntaxTreeNode (curNode : SyntaxTree.Node) (environments : Environment list) =
        if not curNode.IsTerminal then
            let curChildren = syntaxTree.GetChildren curNode

            match curNode.NodeType with
            | TypedHeaplet heapletType ->
                //Note this production (it's going to be the same every time, but this unifies the handling)
                let nodeFeatures = SparseFeatures.union heapFeatures (SparseFeatures())
                nodeTypeToFeatureAndProductionPairs.Add (curNode.NodeType, (getChosenProduction curNode, nodeFeatures))

                let lambdaNode = Seq.find (fun (n : Node) -> n.NodeType = LambdaBinding) curChildren
                let newEnvironmentsInformation = 
                    ComputeNewEnvironments environments syntaxTree curNode heapletType existentialsFeatures

                //Visit the nested formula:
                match newEnvironmentsInformation with
                | Some (nestedSymheapNode, oldAndNewEnvironments) ->
                    let newEnvironments = List.map (fun (_, _, newEnvironment) -> newEnvironment) oldAndNewEnvironments
                    visitSyntaxTreeNode nestedSymheapNode newEnvironments
                | None -> ()

                //Visit the expression arguments of this (with original variable bindings)
                for childNode in curChildren do
                    match childNode.NodeType with
                    | Expression ->
                        visitSyntaxTreeNode childNode environments
                    | _ -> ()

                //Compute features for the lambda node, which we skipped over in the recursive call:
                let newEnvironmentsWithSubheapStarts =
                    match newEnvironmentsInformation with
                    | None ->
                        //No nested heap / no new var bindings. Still note something for the lambda node (i.e., that there is none):
                        []
                    | Some (_, oldAndNewEnvironments) ->
                        List.map (fun (oldEnv, subheapStart, _) -> (oldEnv, subheapStart)) oldAndNewEnvironments
                let lambdaFeatures = ComputeLambdaFeatures newEnvironmentsWithSubheapStarts syntaxTree lambdaNode
                nodeTypeToFeatureAndProductionPairs.Add
                    (LambdaBinding, (getChosenProduction lambdaNode, lambdaFeatures))

                let lambdaChild = syntaxTree.GetChildren lambdaNode |> Seq.head
                match lambdaChild.NodeType with
                | TypedLambdaBinding _ ->
                    nodeTypeToFeatureAndProductionPairs.Add
                        (lambdaChild.NodeType,
                            (getChosenProduction lambdaChild,
                             SparseFeatures()))
                | _ -> ()
            | Expression ->
                let chosenExpression = syntaxTree.GetNameFromExpressionNode curNode
                let thisExprFeatures = ComputeExpressionFeatures usedVarNames environments syntaxTree curNode chosenExpression
                let exprPosId = syntaxTree.GetExprNodePosDescriptor curNode
                if not thisExprFeatures.IsEmpty then
                    exprFeatureGroups.Add (exprPosId, thisExprFeatures)
            | PureFormula -> () //This does not go through the ML part. Don't extract, don't recurse
            |_ ->
                let nodeFeatures =
                    match curNode.NodeType with
                    | Heaplets ->
                         ComputeHeapletsFeatures environments usedVarNames syntaxTree curNode
                    | Heaplet ->
                         ComputeHeapletFeatures environments usedVarNames syntaxTree curNode
                    // These are implicitly handled above:
                    | Variable
                    | Symheap
                    | LambdaBinding -> 
                        SparseFeatures()
                    | _ -> 
                        SparseFeatures.union heapFeatures (SparseFeatures())
                if nodeFeatures.Count > 0 && curNode.NodeType <> ExistentialBinding then
                    nodeTypeToFeatureAndProductionPairs.Add (curNode.NodeType, (getChosenProduction curNode, nodeFeatures))
                for childNode in curChildren do
                    visitSyntaxTreeNode childNode environments

    visitSyntaxTreeNode syntaxTree.root environments 

    (nodeTypeToFeatureAndProductionPairs, !existentialsFeatures, exprFeatureGroups)
