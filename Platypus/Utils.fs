module Utils

let equalsOn f x (yobj:obj) =
    match yobj with
    | :? 'T as y -> (f x = f y)
    | _ -> false

let hashOn f x =  hash (f x)

let compareOn f x (yobj: obj) =
    match yobj with
    | :? 'T as y -> compare (f x) (f y)
    | _ -> invalidArg "yobj" "cannot compare values of different types"

let curry f a b = f (a, b)
let uncurry f (a, b) = f a b
let sigmoid t = 1. / (1. + exp -t)

type Map<'Key,'Value when 'Key : comparison> with
    member m.Keys = seq {for kv in m -> kv.Key}
    member m.Values = seq {for kv in m -> kv.Value}
    member m.Items = seq {for kv in m -> (kv.Key, kv.Value)}
    member m.findWithDefault key def = defaultArg (m.TryFind key) def
    static member FindWithDefault key def (m: Map<'Key, 'Value>) = m.findWithDefault key def
    static member Concat (ms: Map<'Key, 'Value> list) =
        let mutable result = Map.empty
        for m in List.rev ms do
            for KeyValue(k, v) in m do
                result <- result.Add(k, v :: result.findWithDefault k [])
        result
    static member addMany (m : Map<'Key, 'Value>) (kvs : ('Key * 'Value) seq) =
        Seq.fold (fun result (key, value) -> Map.add key value result) m kvs
    static member union (m1: Map<'Key, 'Value>) (m2: Map<'Key, 'Value>) =
        let mutable result = m1
        for KeyValue(k, v) in m2 do
            result <- result.Add(k, v)
        result
    static member unionMany (ms: Map<'Key, 'Value> list) =
        match ms with
        | [] -> Map.empty
        | (firstM::restMs) -> List.fold (fun res m -> Map.union res m) firstM restMs
    static member singleton key value =
        Map.empty |> Map.add key value

type Set<'T when 'T : comparison> with
    static member addAll (toAdd : 'T seq) (baseSet : Set<'T>) =
        Seq.fold (fun res toAdd -> Set.add toAdd res) baseSet toAdd
    static member containsAll (toCheck : 'T seq) (set : Set<'T>) =
        Seq.fold (fun res toCheck -> res && Set.contains toCheck set) true toCheck
    /// Remove all elements of toRemove from baseSet.
    static member removeAll (toRemove : Set<'T>) (baseSet : Set<'T>) =
        Set.fold (fun res toRemove -> Set.remove toRemove res) baseSet toRemove
    static member unionMap f s =
        Set.fold (fun acc v -> f v |> Set.union acc) Set.empty s

type List<'T> with
    static member contains e l =
        None <> List.tryFind (fun t -> e = t) l
    ///Applies f to the elementfs of l1, then appends l2
    static member mapAppend f l1 l2 =
        List.foldBack (fun v acc -> (f v)::acc) l1 l2
    static member concatMap f l1 =
        List.foldBack (fun v acc -> (f v)@acc) l1 []
    static member take (n : int) (l : List<'T>) =
        if (n <= 0) then
            []
        else
            match l with
            | [] ->
                invalidArg "l" (sprintf "Trying to take %i elements from empty list" n)
            | (x::xs) -> x :: (List.take (n - 1) xs)
    static member takeAtMost (n : int) (l : List<'T>) =
        if (n <= 0) then
            []
        else
            match l with
            | [] -> []
            | (x::xs) -> x :: (List.takeAtMost (n - 1) xs)
    static member takeWhile (pred : 'T -> bool) (l : List<'T>) : List<'T> =
        match l with
        | [] -> []
        | (x::xs) ->
            if pred x then
                x :: (List.takeWhile pred xs)
            else
                []
    static member filteri (predicate : int -> 'T -> bool) (l : List<'T>) =
        let rec filteri idx predicate l =
            match l with
            | [] -> []
            | (x :: xs) ->
                if predicate idx x then
                    x :: filteri (idx + 1) predicate xs
                else
                    filteri (idx + 1) predicate xs
        filteri 0 predicate l
    static member collecti (mapper : int -> 'T -> 'U list) (l : List<'T>) =
        let rec collecti idx mapper l =
            match l with
            | [] -> []
            | (x :: xs) -> (mapper idx x) @ collecti (idx + 1) mapper xs
        collecti 0 mapper l
    static member unzip7 l =
        List.foldBack
            (fun (x1,x2,x3,x4,x5,x6,x7) (xs1,xs2,xs3,xs4,xs5,xs6,xs7) ->
                (x1::xs1,x2::xs2,x3::xs3,x4::xs4,x5::xs5,x6::xs6,x7::xs7))
            l
            ([],[],[],[],[],[],[])
    static member count pred l =
        let rec count acc pred l =
            match l with
            | [] -> acc
            | (x :: xs) ->
                if pred x then
                    count (acc + 1) pred xs
                else
                    count acc pred xs
        count 0 pred l
    ///Applies the given mapper to all pairs of values
    static member mapOverPairs (mapper : 'T1 -> 'T2 -> 'T3) (l1 : 'T1 list) (l2 : 'T2 list) : 'T3 list =
        List.collect (fun v1 -> List.map (fun v2 -> mapper v1 v2) l2) l1

module Seq =
    let collecti (mapper : int -> 'T -> 'U list) (l : seq<'T>) =
        let rec collecti idx l =
            if Seq.isEmpty l then
                Seq.empty
            else
                Seq.append (mapper idx (Seq.head l)) (collecti (idx + 1) (Seq.skip 1 l))
        collecti 0 l

    /// Partitions a sequence into two lists l1, l2, where all elements of l1 satisfy pred, and all of l2 don't.
    /// Note: Does not preserve order, and evaluates eagerly.
    let partition (pred : 'T -> bool) (l : seq<'T>) =
        let mutable l1 = []
        let mutable l2 = []
        for e in l do
            if pred e then
                l1 <- e :: l1
            else
                l2 <- e :: l2
        (l1, l2)

    let repeat n v = [ for _ in 1..n do yield v ]

    let countIf (pred : 'T -> bool) (l : seq<'T>) =
        let mutable res = 0
        for e in l do
            if pred e then
                res <- res + 1
        res

    let fold2 (folder : 'State -> 'T1 -> 'T2 -> 'State) (state : 'State) (seq1 : 'T1 seq) (seq2 : 'T2 seq) : 'State =
        let enum1 = seq1.GetEnumerator()
        let enum2 = seq2.GetEnumerator()
        let mutable state = state
        while enum1.MoveNext() do
            if not (enum2.MoveNext()) then
                invalidArg "enum2" "Second sequence shorter than first."
            state <- folder state enum1.Current enum2.Current
        if enum2.MoveNext() then
            invalidArg "enum1" "First sequence shorter than second."
        state

    let contains (v : 'T) (seq : 'T seq) : bool =
        Seq.exists ((=) v) seq

    let maxIndexBy (p : 'T -> 'S when 'S : comparison) (vs : 'T seq) =
        if Seq.isEmpty vs then
            -1
        else
            let mutable maxIndex = 0
            let mutable maxValue = p (Seq.head vs)
            let vs = Seq.skip 1 vs
            let mutable index = 1
            for v in vs do
                let pv = p v
                if pv > maxValue then
                    maxValue <- pv
                    maxIndex <- index
                index <- index + 1
            maxIndex

    let takeWithDefault (def : 'T) n (vs : 'T seq) =
        let backingEnumerator = vs.GetEnumerator()
        let isValid = ref true
        let rec take n =
            if n <= 0 then
                []
            else
                isValid := backingEnumerator.MoveNext()
                let nextVal =
                    if !isValid then
                        backingEnumerator.Current
                    else
                        def
                nextVal :: take (n - 1)
        take n

    let fprodBy (p : 'T -> float) (vs : 'T seq) =
        Seq.fold (fun r v -> r * (p v)) LanguagePrimitives.GenericOne<float> vs

type System.Collections.Generic.Dictionary<'TKey, 'TValue> with
    member self.TryFind key =
        match self.TryGetValue key with
        | (true, res) -> Some res
        | (false, _)  -> None
    member self.GetWithDefault key defaultValue =
        match self.TryGetValue key with
        | (true, res) -> res
        | (false, _)  -> defaultValue

    member self.AddAll (keyValues : seq<'TKey * 'TValue>) =
        keyValues |> Seq.iter self.Add

    member self.AddAll (keyValues : seq<System.Collections.Generic.KeyValuePair<'TKey, 'TValue>>) =
        keyValues |> Seq.iter (fun kv -> self.Add (kv.Key, kv.Value))

    member self.RemoveAll (keys : seq<'TKey>) =
        keys |> Seq.iter (fun k -> self.Remove k |> ignore)

type System.Collections.Generic.HashSet<'T> with
    member self.AddAll (values : 'T seq) =
        Seq.iter (fun v -> self.Add v |> ignore) values

type System.Collections.Generic.List<'T> with
    member self.AddAll (values : 'T seq) =
        Seq.iter (fun v -> self.Add v) values

type SetMap<'Key, 'Value when 'Value : comparison and 'Key : comparison> =
    {
        backend : Map<'Key, Set<'Value>>
    }
    static member empty : SetMap<'Key, 'Value> = { backend = Map.empty }
    static member ofSeq (mappings : seq<'Key * Set<'Value>>) = { backend = Map.ofSeq mappings }
    static member containsKey k (m : SetMap<'Key, 'Value>) : bool = Map.containsKey k m.backend
    static member getWithEmptyDefault k (m : SetMap<'Key, 'Value>) =
        if Map.containsKey k m.backend then
            m.backend.[k]
        else
            Set.empty
    static member add k v (m : SetMap<'Key, 'Value>) =
        let oldVals = SetMap.getWithEmptyDefault k m
        let newVals = Set.add v oldVals
        let newBackend = m.backend |> Map.add k newVals
        { backend = newBackend } : SetMap<'Key, 'Value>
    static member addMany k vs (m : SetMap<'Key, 'Value>) =
        let oldVals = SetMap.getWithEmptyDefault k m
        let newVals = Set.union vs oldVals
        let newBackend = m.backend |> Map.add k newVals
        { backend = newBackend } : SetMap<'Key, 'Value>

    member self.Item k = self.backend.[k]

type KeyValueAsPairEnumerator<'Key, 'Value> (backingEnumerator : System.Collections.Generic.IEnumerator<System.Collections.Generic.KeyValuePair<'Key, 'Value>>) =
    interface System.Collections.Generic.IEnumerator<'Key * 'Value> with
        member __.Current with get () = (backingEnumerator.Current.Key, backingEnumerator.Current.Value)
    interface System.Collections.IEnumerator with
        member __.MoveNext () = backingEnumerator.MoveNext ()
        member __.Current with get() = backingEnumerator.Current |> box
        member __.Reset () = backingEnumerator. Reset ()
    interface System.IDisposable with
        member __.Dispose () = backingEnumerator.Dispose ()

type ListDictionary<'Key, 'Value when 'Key : equality and 'Value : equality>(oldBackingDictionary : System.Collections.Generic.Dictionary<'Key, 'Value list>) =
    let backingDictionary = System.Collections.Generic.Dictionary(oldBackingDictionary)
    let mutable hashCodeCache = None
    member __.BackingDictionary with private get () = backingDictionary
    member __.HashCodeCache
        with private get () = hashCodeCache
        and private  set v  = hashCodeCache <- v

    new () = ListDictionary(System.Collections.Generic.Dictionary())
    new (oldDictionary : ListDictionary<'Key, 'Value>) = ListDictionary(oldDictionary.BackingDictionary)

    ///// Accessing entries:
    member self.Item
        with get key       =
            match backingDictionary.TryGetValue key with
            | (true, res) -> res
            | (false, _)  -> []
        and  set key value =
            self.HashCodeCache <- None
            backingDictionary.[key] <- value

    ///// Adding, removing and replacing single entries or full entry seqs:
    /// Adds 'value' to the bindings for 'key'. Does not replace existing bindings.
    member self.Add ((key, value) : ('Key * 'Value)) =
        self.HashCodeCache <- None
        match backingDictionary.TryGetValue key with
        | (true, res) -> backingDictionary.[key] <- value :: res
        | (false, _)  -> backingDictionary.[key] <- [value]
    member self.AddMany ((key, value) : ('Key * 'Value list)) =
        self.HashCodeCache <- None
        match backingDictionary.TryGetValue key with
        | (true, res) -> backingDictionary.[key] <- value @ res
        | (false, _)  -> backingDictionary.[key] <- value
    member self.Remove key =
        self.HashCodeCache <- None
        backingDictionary.Remove key
    member self.Replace key value =
        self.HashCodeCache <- None
        backingDictionary.[key] <- [value]
    member self.ReplaceList key valueList =
        self.HashCodeCache <- None
        backingDictionary.[key] <- valueList

    member __.ContainsKey key =
       backingDictionary.ContainsKey key

    ///// Functional basics:
    member self.Map (f : 'Value list -> 'Value list) =
        self.HashCodeCache <- None
        for key in backingDictionary.Keys do
            backingDictionary.[key] <- f backingDictionary.[key]
    member __.Iter (action : 'Key -> 'Value list -> Unit) =
        backingDictionary |> Seq.iter (fun t -> action t.Key t.Value)
    member __.Fold (folder : 'T -> 'Key -> 'Value list -> 'T) initialState =
        backingDictionary |> Seq.fold (fun state t -> folder state t.Key t.Value) initialState

    ///// Helpers to iterate over contents:
    member __.Keys = backingDictionary.Keys
    member __.Values = backingDictionary.Values
    member __.Bindings = seq { for KeyValue(k,vs) in backingDictionary do for v in vs do yield (k,v) }
    interface System.Collections.Generic.IEnumerable<'Key * ('Value list)> with
        member __.GetEnumerator () = new KeyValueAsPairEnumerator<'Key, 'Value list>(backingDictionary.GetEnumerator()) :> _
    interface System.Collections.IEnumerable with
        member __.GetEnumerator () = new KeyValueAsPairEnumerator<'Key, 'Value list>(backingDictionary.GetEnumerator()) :> _

    override self.Equals other =
        match other with
        | :? ListDictionary<'Key, 'Value> as otherLD->
            self.BackingDictionary.Count = otherLD.BackingDictionary.Count
            && (self.Fold (fun acc k vs -> acc && otherLD.[k] = vs) true)
        | _ -> false
    override self.GetHashCode () =
        if hashCodeCache.IsNone then
            hashCodeCache <-
                Some (3 + self.Fold (fun s k vs -> s + 5 * k.GetHashCode() + 7 * vs.GetHashCode()) 0)
        hashCodeCache.Value

type SetDictionary<'Key,'Value when 'Key : equality and 'Value : comparison>() =
    let backingDict = System.Collections.Generic.Dictionary()

    ///// Accessing entries:
    member __.Item
        with get key =
            match backingDict.TryGetValue key with
            | (true, set) ->
                set
            | (false, _) ->
                let set = System.Collections.Generic.HashSet()
                backingDict.[key] <- set
                set
        and  set key value = backingDict.[key] <- value

    ///// Adding, removing and replacing single entries or full entry seqs:
    member __.Add (key, value) =
        match backingDict.TryGetValue key with
        | (true, set) ->
            set.Add value
        | (false, _)  ->
            backingDict.[key] <- System.Collections.Generic.HashSet([value])
            true
    member self.AddMany keyValuePairs =
        Seq.iter (self.Add >> ignore) keyValuePairs
    member self.Union (otherDict : SetDictionary<'Key, 'Value>) =
        self.AddMany otherDict.Bindings
    member __.Remove key =
        backingDict.Remove key
    member __.RemoveKeyVal key value =
        backingDict.[key].Remove value

    member __.ContainsKey key =
       backingDict.ContainsKey key

    ///// Functional basics:
    /// Note that the argument of f is the (mutable) backing set in the dictionary, and hence changes remain visible
    member __.Map (f : System.Collections.Generic.HashSet<'Value> -> System.Collections.Generic.HashSet<'Value>) =
        for key in backingDict.Keys do
            backingDict.[key] <- f backingDict.[key]
    member __.Iter (action : 'Key -> System.Collections.Generic.HashSet<'Value> -> Unit) =
        backingDict |> Seq.iter (fun t -> action t.Key t.Value)
    member __.Fold (folder : 'T -> 'Key -> System.Collections.Generic.HashSet<'Value> -> 'T) initialState =
        backingDict |> Seq.fold (fun state t -> folder state t.Key t.Value) initialState

    ///// Helpers to iterate over contents:
    member __.Keys = backingDict.Keys
    member __.Values = backingDict.Values
    member __.Bindings = seq { for KeyValue(k,vs) in backingDict do for v in vs do yield (k,v) }
    interface System.Collections.Generic.IEnumerable<'Key * System.Collections.Generic.HashSet<'Value>> with
        member __.GetEnumerator () = new KeyValueAsPairEnumerator<'Key, System.Collections.Generic.HashSet<'Value>>(backingDict.GetEnumerator()) :> _
    interface System.Collections.IEnumerable with
        member __.GetEnumerator () = new KeyValueAsPairEnumerator<'Key, System.Collections.Generic.HashSet<'Value>>(backingDict.GetEnumerator()) :> _


[<AbstractClass>]
type Graph<'Node, 'Label when 'Node : comparison and 'Label : comparison>() =
    abstract member GetNodes : unit -> 'Node seq
    abstract member GetInEdges : 'Node -> Set<'Node * 'Label>
    abstract member GetOutEdges : 'Node -> Set<'Label * 'Node>
    abstract member GetAllEdges : unit -> ('Node * 'Label * 'Node) seq
    default self.GetAllEdges() = self.GetNodes() |> Seq.collect (fun v -> self.GetOutEdges v |> Set.map (fun (l, v') -> (v, l, v')))


    member self.toDot (nodeLabels : Map<string, 'Node>) outStream =
        fprintfn outStream "digraph heap {"

        let mutable potentialEdges = []
        for KeyValue(label, value) in nodeLabels do
            fprintfn outStream " lab%s [shape=circle, color=red, label=\"%s: %s\"];" label label (value.ToString())
            potentialEdges <- (sprintf "lab%s" label, "", sprintf "node%s" (value.ToString())) :: potentialEdges

        let vToDotNode v = sprintf "node%A" v
        let mutable defNodes = Set.empty
        for source in self.GetNodes () do
            for (label, target) in self.GetOutEdges source do
                let sourceNode = vToDotNode source
                defNodes <- Set.add sourceNode defNodes
                fprintfn outStream " %s [shape=record, color=black, label=\"%s\"];" sourceNode (source.ToString())
                potentialEdges <- (sourceNode, label.ToString(), vToDotNode target) :: potentialEdges

        for (src, label, dst) in potentialEdges do
            if Set.contains dst defNodes then
                fprintfn outStream " %s -> %s [label=\"%s\"];" src dst label

        fprintfn outStream "};"

type ImmutableGraph<'Node, 'Label when 'Node : comparison and 'Label : comparison>
        ( Nodes : Set<'Node>
        , InEdges : SetMap<'Node, 'Node * 'Label>
        , OutEdges : SetMap<'Node, 'Label * 'Node>) =
    inherit Graph<'Node, 'Label>()

    override __.GetNodes () = Nodes :> _
    override __.GetOutEdges v = SetMap.getWithEmptyDefault v OutEdges
    override __.GetInEdges v = SetMap.getWithEmptyDefault v InEdges

    static member Empty =
        ImmutableGraph
            ( Set.empty
            , SetMap<'Node, 'Node * 'Label>.empty
            , SetMap<'Node, 'Label * 'Node>.empty)

    member __.AddEdge v1 l v2 =
        ImmutableGraph
            ( Nodes |> Set.add v1 |> Set.add v2
            , InEdges |> SetMap.add v2 (v1, l)
            , OutEdges |> SetMap.add v1 (l, v2))

    override self.Equals other =
        match other with
        | :? ImmutableGraph<'Node, 'Label> as otherGraph->
            Seq.compareWith Operators.compare (self.GetNodes ()) (otherGraph.GetNodes ()) = 0
            && Seq.compareWith Operators.compare (self.GetAllEdges ()) (otherGraph.GetAllEdges ()) = 0
        | _ -> false
    override self.GetHashCode () =
        3 + (Seq.fold (fun h n -> h + 5 * n.GetHashCode()) 0 (self.GetNodes()))
          + (Seq.fold (fun h e -> h + 7 * e.GetHashCode()) 0 (self.GetAllEdges()))

type MutableGraph<'Node, 'Label when 'Node : comparison and 'Label : comparison>() =
    inherit Graph<'Node, 'Label>()
    let Nodes = System.Collections.Generic.HashSet()
    let OutEdges = System.Collections.Generic.Dictionary()
    let InEdges = System.Collections.Generic.Dictionary()

    let mutable hashCodeCache = None
    member __.HashCodeCache
        with private get () = hashCodeCache
        and private  set v  = hashCodeCache <- v

    member self.AddEdge v1 l v2 =
        self.HashCodeCache <- None
        Nodes.Add(v1) |> ignore
        Nodes.Add(v2) |> ignore
        OutEdges.[v1] <- Set.add (l, v2) (self.GetOutEdges v1)
        InEdges.[v2] <- Set.add (v1, l) (self.GetInEdges v2)

    override __.GetNodes () = Nodes :> _
    override __.GetOutEdges v =
        match OutEdges.TryGetValue v with
        | (true, result) -> result
        | (false, _)     -> Set.empty
    override __.GetInEdges v =
        match InEdges.TryGetValue v with
        | (true, result) -> result
        | (false, _)     -> Set.empty

    override self.Equals other =
        match other with
        | :? MutableGraph<'Node, 'Label> as otherGraph->
            Seq.compareWith Operators.compare (self.GetNodes ()) (otherGraph.GetNodes ()) = 0
            && Seq.compareWith Operators.compare (self.GetAllEdges ()) (otherGraph.GetAllEdges ()) = 0
        | _ -> false
    override self.GetHashCode () =
        if hashCodeCache.IsNone then
            hashCodeCache <-
                Some (3 + (Seq.fold (fun h n -> h + 5 * n.GetHashCode()) 0 (self.GetNodes()))
                        + (Seq.fold (fun h e -> h + 7 * e.GetHashCode()) 0 (self.GetAllEdges())))
        hashCodeCache.Value


let private FieldNameToIntId = System.Collections.Generic.Dictionary<string, int>()

//This is our default, and if we actually parse things, we will overwrite it.
let private DataFieldIds =
    let set = System.Collections.Generic.HashSet<int>()
    set.Add 0 |> ignore
    set
let ClearDataFields() = DataFieldIds.Clear()

let private NextFieldId = ref 0
let GetIdForFieldName fieldName =
    match FieldNameToIntId.TryFind fieldName with
    | Some id -> id
    | None ->
        let newId = !NextFieldId
        incr NextFieldId
        FieldNameToIntId.Add(fieldName, newId)
        if fieldName.EndsWith "data" then
            DataFieldIds.Add newId |> ignore
        newId
let GetFieldNameForId fieldId =
    (FieldNameToIntId |> Seq.find (fun kv' -> kv'.Value = fieldId)).Key

let KnownFieldNames = FieldNameToIntId.Keys
let KnownFieldIds = FieldNameToIntId.Values
let KnownDataFieldIds = DataFieldIds

/// Graphs representing heaps have this type as edge labels, because fields can be data fields or pointer fields
type HeapLabel (labelId : int) =
    member __.Id = labelId
    override __.ToString() = string labelId

    static member GetId (self : HeapLabel) = self.Id
    static member IsDataField (self : HeapLabel) = DataFieldIds.Contains self.Id

    static member FromString (str: string) =
        let (|Startswith|) pref (str : string) =
            if str.StartsWith(pref) then
                Some  (str.Substring(pref.Length))
            else
                None

        match str with
        | Startswith "I" (Some intstr) -> HeapLabel (int intstr)
        | Startswith "A" (Some intstr) -> HeapLabel (int intstr)
        | _ -> HeapLabel (int str)
        //| _ -> failwith (sprintf "Unknown format for a label: %s" str)


    override x.Equals y = equalsOn HeapLabel.GetId x y
    override x.GetHashCode() = hashOn HeapLabel.GetId x
    interface System.IComparable with
        member x.CompareTo y = compareOn HeapLabel.GetId x y

type AnnotatedGraph (backingGraph : Graph<bigint, HeapLabel>) =
    let mutable sccs = null
    let reachableNodes = System.Collections.Generic.Dictionary()
    let reachableNodesViaLabel = System.Collections.Generic.Dictionary()
    let reachableNodesWithoutForbiddenLabelsCache = System.Collections.Generic.Dictionary()
    let mutable nodeToUnigram = null
    let mutable nodeToUnigramDepthPerAddr = System.Collections.Generic.Dictionary()

    member __.BackingGraph = backingGraph

    override self.Equals other =
        match other with
        | :? AnnotatedGraph as otherGraph->
            self.BackingGraph = otherGraph.BackingGraph
        | _ -> false
    override self.GetHashCode () =
        self.BackingGraph.GetHashCode()

    ///Compute all reachable nodes for all nodes (via Floyd-Warshall)
    member private self.ComputeAllReachables () =
        let reachable = System.Collections.Generic.HashSet()
        for v in backingGraph.GetNodes () do
            for (_, u) in self.BackingGraph.GetOutEdges v do
                reachable.Add (v, u) |> ignore
            //reachable.Add (v, v) //for reflexive closure

        for w in backingGraph.GetNodes () do
            for v in backingGraph.GetNodes () do
                for u in backingGraph.GetNodes () do
                    if reachable.Contains (w, u) && reachable.Contains (v, w) then
                        reachable.Add (v, u) |> ignore

        for v in backingGraph.GetNodes () do
            reachableNodes.[v] <- System.Collections.Generic.HashSet(backingGraph.GetNodes () |> Seq.filter (fun w -> reachable.Contains (v, w)))

    ///Compute all nodes reachable from v (via DFS) (non-reflexive)
    member private self.ComputeReachables v =
        let reachable = System.Collections.Generic.HashSet()
        let mutable stack = []
        for (_, v') in self.BackingGraph.GetOutEdges v do
            stack <- v' :: stack
        while not(List.isEmpty stack) do
            let curNode = List.head stack
            stack <- List.tail stack

            if reachable.Add curNode then
                for (_, succNode) in self.BackingGraph.GetOutEdges curNode do
                    stack <- succNode :: stack
        reachableNodes.[v] <- reachable

    ///Computes reachableNodesViaLabel: list of sets of reachable nodes by following only one label
    member private self.ComputeReachablesWithOneLabel x =
        reachableNodesViaLabel.[x] <- []
        for (label, addr) in self.BackingGraph.GetOutEdges x do
            let reachableViaLabel = System.Collections.Generic.HashSet()
            let mutable stack = [addr]
            while not (List.isEmpty stack) do
                let v = List.head stack
                stack <- List.tail stack

                if reachableViaLabel.Add v then
                    for (_, v') in self.BackingGraph.GetOutEdges v |> Set.filter (fun (l, _) -> l = label) do
                        stack <- v' :: stack

            reachableNodesViaLabel.[x] <- (label, reachableViaLabel) :: reachableNodesViaLabel.[x]

    ///Compute SCCs (via Tarjan, cf "Depth-first search and linear graph algorithms", page 157)
    member private self.ComputeSCCs () =
        let lowlink = System.Collections.Generic.Dictionary()
        let number = System.Collections.Generic.Dictionary()

        let stack = System.Collections.Generic.Stack()
        let stackContents = System.Collections.Generic.HashSet()

        sccs <- System.Collections.Generic.List()
        let i = ref 1
        let rec strongconnect v =
            if v <> bigint.Zero then //Ignore 0. We don't do that.
                number.[v] <- !i
                lowlink.[v] <- !i
                i := !i + 1
                stack.Push v
                stackContents.Add v |> ignore

                for (_, w) in self.BackingGraph.GetOutEdges v do
                    if w <> bigint.Zero then
                        if not(number.ContainsKey w) then
                            strongconnect w
                            lowlink.[v] <- min lowlink.[v] lowlink.[w]
                        else if number.[w] < number.[v] then
                            if stackContents.Contains w then
                                lowlink.[v] <- min lowlink.[v] number.[w]
                if lowlink.[v] = number.[v] then
                    let newComponent = System.Collections.Generic.HashSet()
                    let numberV = number.[v]
                    while stack.Count > 0 && number.[stack.Peek()] >= numberV do
                        let w = stack.Pop ()
                        stackContents.Remove w |> ignore
                        newComponent.Add w |> ignore

                    //Add to result, but remove trivial SCCs without self-cycles:
                    if newComponent.Count > 1 || (Seq.exists (fun (_, w) -> w = v) (self.BackingGraph.GetOutEdges v)) then
                        sccs.Add newComponent

        for w in backingGraph.GetNodes () do
            if not (number.ContainsKey w) then
                strongconnect w

    member private self.ComputeUnigrams () =
        nodeToUnigram <- System.Collections.Generic.Dictionary()
        for v in backingGraph.GetNodes () do
            if v <> bigint.Zero then
                let vInEdges = self.BackingGraph.GetInEdges v
                let vOutEdges = self.BackingGraph.GetOutEdges v
                nodeToUnigram.Add (v, (Set.count vInEdges, Set.count vOutEdges))

    member private self.ComputeUnigramDepthForAddr addr =
        //Ensure that unigram information is there:
        if nodeToUnigram = null then self.ComputeUnigrams ()

        let nodeToUnigramDepth = System.Collections.Generic.Dictionary()
        let addToMinDepth (minDepthDict : System.Collections.Generic.Dictionary<bigint, int>) addr newDepth =
            let mutable curDepth = 0
            if minDepthDict.TryGetValue (addr, &curDepth) then
                minDepthDict.[addr] <- min curDepth newDepth
            else
                minDepthDict.[addr] <- newDepth
        let expanded = System.Collections.Generic.HashSet()
        /// Triples (node, label of the edge leading to node, depth computed for this)
        let queue = System.Collections.Generic.Queue<bigint * HeapLabel * int> ([(addr, HeapLabel -1, 0)])

        while queue.Count > 0 do
            let (v, labelToV, vDepth) = queue.Dequeue()

            if nodeToUnigram.ContainsKey v && expanded.Add v then
                addToMinDepth nodeToUnigramDepth v vDepth

                let vUnigram = nodeToUnigram.[v]

                for (labelToV', v') in self.BackingGraph.GetOutEdges v do
                    if v' <> bigint.Zero then
                        let v'Unigram = nodeToUnigram.[v']

                        // Only increase the count when both of the following conditions hold:
                        // (1) Label of the incoming edge to current node is different from incoming edge to previous node
                        // (2) Current node is different from previous node (i.e., (indeg, outdeg) doesn’t match)
                        let v'Depth = if labelToV' <> labelToV && vUnigram <> v'Unigram then vDepth + 1 else vDepth

                        queue.Enqueue (v', labelToV', v'Depth)
        nodeToUnigramDepthPerAddr.[addr] <- nodeToUnigramDepth
        nodeToUnigramDepth

    member self.GetReachable v =
        match reachableNodes.TryGetValue v with
        | (true, result) ->
            result
        | (false, _) ->
            self.ComputeReachables v
            reachableNodes.[v]

    member self.IsReachable v v' =
        let reachables = self.GetReachable v
        reachables.Contains v'

    member self.IsReachableViaOneLabel v v' =
        let mutable cachedReachables = []
        if not (reachableNodesViaLabel.TryGetValue (v, &cachedReachables)) then
            self.ComputeReachablesWithOneLabel v
            cachedReachables <- reachableNodesViaLabel.[v]
        cachedReachables |> Seq.exists (fun (_, reachables) -> reachables.Contains v')

    /// Here, we only consider non-trivial SCCs (i.e. those where for each v, v' there exists a non-trivial path from v to v')
    member self.GetSCCs ()=
        if sccs = null then
            self.ComputeSCCs ()
        sccs

    member self.IsInSCC v =
        self.GetSCCs () |> Seq.exists (fun (scc : System.Collections.Generic.HashSet<bigint>) -> scc.Contains v)

    member self.SomeInSCC (vs : System.Collections.Generic.HashSet<bigint>) =
        self.GetSCCs ()
        |> Seq.exists (fun (scc : System.Collections.Generic.HashSet<bigint>) -> scc.Overlaps vs)

    member self.GetNodeToUnigram () =
        if nodeToUnigram = null then
            self.ComputeUnigrams ()
        nodeToUnigram

    member self.GetNodeToUnigramDepth addr =
        match nodeToUnigramDepthPerAddr.TryGetValue addr with
        | (true, res) -> res
        | (false, _) -> self.ComputeUnigramDepthForAddr addr

    ///Returns true iff there is a path from x to y that does not use a node in forbiddenNodes
    member self.IsReachableWithoutForbidden x y (forbiddenNodes : bigint seq) (forbiddenLabels : System.Collections.Generic.HashSet<int>) =
        let seen = System.Collections.Generic.HashSet(forbiddenNodes)
        let stack = System.Collections.Generic.Stack()
        for (_, reachedAddr) in self.BackingGraph.GetOutEdges x |> Seq.filter (fun (l, _) -> not <| forbiddenLabels.Contains l.Id) do
            stack.Push reachedAddr

        let mutable res = false
        while stack.Count > 0 && not res do
            let k = stack.Pop()

            if k = y then
                res <- true
            else
                if seen.Add k then
                    for (_, k') in self.BackingGraph.GetOutEdges k  |> Seq.filter (fun (l, _) -> not <| forbiddenLabels.Contains l.Id) do
                        stack.Push k'

        res
    
    member private self.ComputeReachableNodesWithoutForbiddenLabels x (forbiddenLabels : System.Collections.Generic.HashSet<int>) =
        let seen = System.Collections.Generic.HashSet()
        let stack = System.Collections.Generic.Stack()
        for (_, reachedAddr) in self.BackingGraph.GetOutEdges x |> Seq.filter (fun (l, _) -> not <| forbiddenLabels.Contains l.Id) do
            stack.Push reachedAddr

        while stack.Count > 0 do
            let k = stack.Pop()

            if seen.Add k then
                for (_, k') in self.BackingGraph.GetOutEdges k  |> Seq.filter (fun (l, _) -> not <| forbiddenLabels.Contains l.Id) do
                    stack.Push k'

        seen

    ///Returns true iff there is a path from x to y that does not use a label in forbiddenLabels
    member self.IsReachableWithoutForbiddenLabels x y (forbiddenLabels : System.Collections.Generic.HashSet<int>) =
        match reachableNodesWithoutForbiddenLabelsCache.TryGetValue((x, forbiddenLabels)) with
        | (false, _) ->
            let reachableNodes = self.ComputeReachableNodesWithoutForbiddenLabels x forbiddenLabels
            reachableNodesWithoutForbiddenLabelsCache.[(x, forbiddenLabels)] <- reachableNodes
            reachableNodes.Contains y
        | (true, reachableNodes) ->
            reachableNodes.Contains y

    member self.GetReachableWithoutForbidden x (forbiddenNodes : bigint seq) =
        let forbidden = System.Collections.Generic.HashSet(forbiddenNodes)
        forbidden.Remove x |> ignore
        let seen = System.Collections.Generic.HashSet()
        let mutable stack = [x]

        while not (List.isEmpty stack) do
            let k = List.head stack
            stack <- List.tail stack

            if not(forbidden.Contains k) && seen.Add k then
                for (_, k') in self.BackingGraph.GetOutEdges k do
                    stack <- k' :: stack
        seen

type HeapGraph (graph : AnnotatedGraph, subheapStartsToExistentials : ListDictionary<bigint, bigint> option) =
    new(graph : AnnotatedGraph) =
        HeapGraph(graph, None)

    member __.Graph with get () = graph
    member __.HasExistentialInformation = subheapStartsToExistentials.IsSome
    member __.SubheapStartsToExistentials = subheapStartsToExistentials.Value

    override self.Equals other =
        match other with
        | :? HeapGraph as otherGraph->
            self.Graph = otherGraph.Graph
            && self.HasExistentialInformation = otherGraph.HasExistentialInformation
            && (   (self.HasExistentialInformation && self.SubheapStartsToExistentials = otherGraph.SubheapStartsToExistentials)
                || (not self.HasExistentialInformation))
        | _ -> false
    override self.GetHashCode () =
        3 + 5 * self.Graph.GetHashCode() + (if self.HasExistentialInformation then 7 * self.SubheapStartsToExistentials.GetHashCode() else 0)

let rec allTuples arity seq =
    if arity <= 0 then
        [[]]
    else
           allTuples (arity - 1) seq
        |> List.map (fun t -> seq |> List.map (fun e -> e::t))
        |> List.concat

// http://rosettacode.org/wiki/Knuth_shuffle
let KnuthShuffle (pnrg : System.Random) (lst : 'a array) =
    let Swap i j =
        let item = lst.[i]
        lst.[i] <- lst.[j]
        lst.[j] <- item
    let ln = lst.Length
    [0..(ln - 2)] |> Seq.iter (fun i -> Swap i (pnrg.Next(i, ln)))

/// Find a fresh variable name based on "v" that does not occur in "knownVars", adds it to that set
let freshVarCounter = ref 0
let freshVar (knownVars : System.Collections.Generic.HashSet<string>) (v : string) =
    let mutable curName = v + "_" + string !freshVarCounter
    while not (knownVars.Add curName) do
        freshVarCounter := !freshVarCounter + 1
        curName <- v + "_" + string !freshVarCounter
    curName

//For a list of sets (repr. as lists), computes the cartesian product (as all sets that contains exactly one element of each of the passed lists)
let cartesianProduct listOfSets =
    let rec cartesianProduct' listOfSets acc =
        match listOfSets with
        | [] -> []
        | oneSet::[] ->
            oneSet |> List.collect (fun e -> List.map (fun res -> e :: res) acc)
        | oneSet::restOfSets ->
            let newAcc =
               oneSet |> List.collect (fun e -> List.map (fun res -> e :: res) acc)
            cartesianProduct' restOfSets newAcc
    cartesianProduct' listOfSets [[]]

let inline incrementCounter (counterDict : System.Collections.Generic.Dictionary<'T, int>) (counterKey : 'T) =
    match counterDict.TryGetValue counterKey with
    | (true, curCounter) -> counterDict.[counterKey] <- 1 + curCounter
    | (false, _)         -> counterDict.[counterKey] <- 1

module Async =
    /// Runs a sequence of computations in parallel, awaits their return and throws away all return values.
    let RunParallely (computations : Async<'T>[]) =
        computations
        |> Async.Parallel
        |> Async.RunSynchronously
        |> ignore

/// A priority queue backed by an array-based binary heap. Larger priorities come first, and
/// priorities are computed by the function provided in the constructor. This computation is
/// not cached, but repeated a lot, and thus this implementation is not suitable for cases
/// where the priority computation is expensive.
type PriorityQueue<'T> (priorityMap : 'T -> int) =
    /// The backing array actually containing all of our beautiful data
    let mutable data = Array.zeroCreate<'T> 8
    /// The next index to be used for insertion.
    //To simplify the remaining implementation, we start with 1, and data[0] will always stay empty.
    let mutable nextIndex = 1

    member private __.Swap i j =
        let temp = data.[i]
        data.[i] <- data.[j]
        data.[j] <- temp

    member private __.DoubleCapacity() =
        let oldData = data
        data <- Array.zeroCreate<'T> (oldData.Length * 2)
        System.Array.Copy (oldData, data, oldData.Length)

    ///Restore heap property, which might be violated by data.[index] being larger than its "parent"
    member private self.Heapify index =
        //We are done for index <= 1, so only consider the others:
        if index > 1 then
            if priorityMap data.[index / 2] < priorityMap data.[index] then
                self.Swap (index / 2) index
                self.Heapify (index / 2)

    ///Restore heap property, which might be violated by data.[index] being smaller that its "children"
    member private self.Trickle index =
        let mutable swapIndex = index
        if 2 * index < nextIndex && priorityMap data.[index] < priorityMap data.[2 * index] then
            swapIndex <- 2 * index
        if 2 * index + 1 < nextIndex && priorityMap data.[swapIndex] < priorityMap data.[2 * index + 1] then
            swapIndex <- 2 * index + 1
        if index <> swapIndex then
            self.Swap index swapIndex
            self.Trickle swapIndex

    member __.Clear () : unit =
       data <- Array.zeroCreate<'T> 8
       nextIndex <- 1

    member self.Peek () : 'T = 
        if self.IsEmpty then
            invalidOp "Can't peek into empty queue."
        data.[1]

    member self.Pop () : 'T=
        if self.IsEmpty then
            invalidOp "Can't pop from empty queue."
        let resultValue = data.[1]
        data.[1] <- data.[nextIndex - 1]
        data.[nextIndex - 1] <- Unchecked.defaultof<'T> //Think of the garbage collector, so destroy link.
        nextIndex <- nextIndex - 1
        self.Trickle 1
        resultValue

    member self.Push (value : 'T) : unit =
        //Enlarge backing data structure if needed
        if nextIndex = data.Length then
            self.DoubleCapacity()
        data.[nextIndex] <- value
        self.Heapify nextIndex
        nextIndex <- nextIndex + 1

    member __.Count with get () = nextIndex - 1
    member __.IsEmpty with get () = nextIndex <= 1
    
    static member inline clear (queue : PriorityQueue<'T>) : unit = queue.Clear()
    static member inline peek (queue : PriorityQueue<'T>) : 'T = queue.Peek()
    static member inline pop (queue : PriorityQueue<'T>) : 'T = queue.Pop()
    static member inline push (value : 'T) (queue : PriorityQueue<'T>) : unit = queue.Push value
    static member inline count (queue : PriorityQueue<'T>) : int = queue.Count
    static member inline isEmpty (queue : PriorityQueue<'T>) : bool = queue.IsEmpty