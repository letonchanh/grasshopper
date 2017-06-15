module State

open Utils
open Program
open System.Linq

type Addr = bigint

type Value =
    | ValInt of bigint
    | ValAddr of Addr

    override self.ToString() =
        match self with
        | ValInt i -> sprintf "%s" (i.ToString ())
        | ValAddr i -> sprintf "%s" (i.ToString ())

    static member FromString (str: string) =
        let (|Startswith|) pref (str : string) =
            let str = str.Trim()
            if str.StartsWith(pref) then
                Some  (str.Substring(pref.Length))
            else
                None

        match str with
        | Startswith "I" (Some intstr) -> ValInt (bigint.Parse intstr)
        | Startswith "A" (Some intstr) -> ValAddr (bigint.Parse intstr)
        | _ -> failwith (sprintf "Unknown format for a value: %s" str)

    static member valSeqToAddrSeq (valSeq : Value seq) =
        valSeq |> Seq.collect (function | ValAddr a -> [a] | ValInt _ -> [])

    static member addrSeqToValSeq (addrSeq : Addr seq) =
        addrSeq |> Seq.map (fun a -> Value.ValAddr a)

    member self.GetValInt() =
        match self with
        | ValInt x -> x
        | _ -> failwith "GetValInt called on non-int value"

    member self.GetValAddr() =
        match self with
        | ValAddr x -> x
        | _ -> failwith "GetValAddr called on non-address value"

[<CustomEquality; NoComparison>]
type VarStack =
    private {
        VarValues : Value [];
        mutable VarToIdxMap : Map<VarName, int>;
    }
    with
        static member empty allVars =
            {
                VarValues = Array.create (Seq.length allVars) (ValInt (bigint 0)) ;
                VarToIdxMap = allVars |> Seq.mapi (fun i v -> (v, i)) |> Map.ofSeq ;
            }
        static member ofMap (m : Map<VarName, Value>) =
            let vs = VarStack.empty m.Keys
            Map.iter vs.Set m
            vs
        member self.Set varName (value : Value) =
            let idx = self.VarToIdxMap.[varName]
            self.VarValues.[idx] <- value
        member self.Get varName =
            let idx = self.VarToIdxMap.[varName]
            self.VarValues.[idx]
        member self.TryGet varName =
            let varIdx = Map.tryFind varName self.VarToIdxMap
            if varIdx = None then None else Some self.VarValues.[varIdx.Value]
        member self.Size with get() = self.VarToIdxMap |> Seq.length
        member self.HasVariable varName = self.VarToIdxMap.ContainsKey varName
        member self.AddrValues with get() = Value.valSeqToAddrSeq self.VarValues
        
        override self.ToString () =
            let newLine = System.Environment.NewLine
            let varString =
                self.VarToIdxMap
                |> Seq.map
                    (fun e -> sprintf "%i (%s): %s" e.Value e.Key (self.VarValues.[e.Value].ToString()))
                |> String.concat ", "
            varString + newLine

        override self.Equals other =
            match other with
            | :? VarStack as otherVarStack ->
                let valuesSame =
                    match (self.VarValues, otherVarStack.VarValues) with
                    | (null, null) -> true
                    | (null, _)
                    | (_, null) -> false
                    | (ourValues, otherValues) -> Enumerable.SequenceEqual(ourValues, otherValues)
                valuesSame && self.VarToIdxMap.Equals(otherVarStack.VarToIdxMap)
            | _ -> false

        override self.GetHashCode () =
            self.VarToIdxMap.GetHashCode() + Seq.fold (fun res v -> 31 * res + v.GetHashCode()) 0 self.VarValues

        interface System.Collections.Generic.IEnumerable<VarName * Value> with
            member self.GetEnumerator () = (self.VarToIdxMap |> Seq.map (fun kv -> (kv.Key, self.Get kv.Key))).GetEnumerator()
        interface System.Collections.IEnumerable with
            member self.GetEnumerator () = (self :> System.Collections.Generic.IEnumerable<VarName * Value>).GetEnumerator() :> _
    end

type Heap =
    {
        addrMap : System.Collections.Generic.Dictionary<bigint, Value>;
        mutable nextFreeAddr : bigint;
    }
    with
        static member empty = { Heap.addrMap = System.Collections.Generic.Dictionary() ; nextFreeAddr = bigint.One}
        member self.set addr value =
            //assert (Map.containsKey addr self.addrMap) //Check that written memory was malloced
            self.addrMap.[addr] <- value

        member self.isAlloced addr =
            self.addrMap.ContainsKey addr

        member self.get addr =
            assert (self.isAlloced addr) //Memory cell was initialized
            self.addrMap.[addr]

        member self.malloc size =
            let res = self.nextFreeAddr;
            self.nextFreeAddr <- self.nextFreeAddr + size + bigint.One; //Add an empty cell in the middle, we use that later one
            for addr in res .. (res+size-bigint.One) do
                self.addrMap.[addr] <- ValInt (bigint.Zero)
            res

        member self.pointsToChunkStart addr =
            self.isAlloced addr && not(self.isAlloced (addr - bigint.One))

        /// returns seq of (offset, value) pairs, in no particular order
        member self.dataInChunk addr =
            assert (self.pointsToChunkStart addr)

            let mutable i = 0
            let mutable res = []
            while self.addrMap.ContainsKey (addr + bigint i) do
                res <- (i, self.get (addr + bigint i))::res
                i <- i + 1
            res

        override self.ToString () =
            let newLine = System.Environment.NewLine
            let heapList =
                   self.addrMap
                |> Seq.map (fun entry ->
                                sprintf "h[%s] = %s" (entry.Key.ToString()) (entry.Value.ToString()))
            (String.concat newLine heapList) + newLine
    end

type State =
    {
        varStack : VarStack;
        heap : Heap;
    }
    with
        static member empty allVars = { varStack = VarStack.empty allVars ; heap = Heap.empty }
        override self.ToString () =
            let newLine = System.Environment.NewLine
            sprintf "Vars: %s%sHeap:%s%s" (self.varStack.ToString()) newLine (self.heap.ToString()) newLine

        member self.asGraph () =
            let res = MutableGraph<bigint, HeapLabel>()
            let stack = System.Collections.Generic.Stack()
            for varValue in self.varStack.VarValues do
                stack.Push varValue
            while stack.Count > 0 do
                match stack.Pop() with
                | ValAddr addr ->
                    if Seq.isEmpty <| res.GetOutEdges addr && self.heap.pointsToChunkStart addr then
                        let newData = self.heap.dataInChunk addr
                        for (offset, value) in newData do
                            match value with
                            | ValInt _ ->
                                //Never add ints to graph: res.AddEdge addr (LabelInt offset) x
                                ()
                            | ValAddr a ->
                                res.AddEdge addr (HeapLabel offset) a
                                stack.Push value
                | _ -> ()
            res

        member self.toDot outStream =
            fprintfn outStream "digraph heap {"

            let potentialEdges = ref []
            for e in self.varStack.VarToIdxMap do
                let varName = e.Key
                let varID = e.Value
                let varVal = self.varStack.Get varName
                fprintfn outStream " var%i [shape=circle, color=red, label=\"%s: %s\"];" varID varName (varVal.ToString())
                potentialEdges := (sprintf "var%i" varID, "", sprintf "chunk%s" (varVal.ToString()))::!potentialEdges

            let definedChunks = ref Set.empty
            for e in self.heap.addrMap do
                let chunkAddr = e.Key
                if self.heap.pointsToChunkStart chunkAddr then //Only print if it's the first in its chunk
                    let chunkValues = ref []
                    let i = ref 0
                    let chunkAddrStr = sprintf "chunk%s" (chunkAddr.ToString())
                    definedChunks := Set.add chunkAddrStr !definedChunks
                    while self.heap.isAlloced (chunkAddr + bigint(!i)) do
                        let chunkValue = self.heap.get (chunkAddr + bigint(!i))
                        chunkValues := chunkValue :: !chunkValues
                        potentialEdges := (chunkAddrStr, sprintf "%i" !i, sprintf "chunk%s" (chunkValue.ToString()))::!potentialEdges
                        i := !i + 1
                    let chunkValues = List.rev !chunkValues

                    let chunkValueStr =
                        chunkValues
                        |> List.map (fun v -> v.ToString())
                        |> String.concat " | "

                    fprintfn outStream " %s [shape=record, color=black, label=\"{%s | { %s } }\"];" chunkAddrStr chunkAddrStr chunkValueStr

            for (src, label, dst) in !potentialEdges do
                if Set.contains dst !definedChunks then
                    fprintfn outStream " %s -> %s [label=\"%s\"];" src dst label

            fprintfn outStream "};"

let stackAndHeapGraphToStream (varStack : VarStack) (heapGraph : Graph<bigint, HeapLabel>) (outStream : System.IO.TextWriter) =
    for (label, value) in varStack do
        outStream.WriteLine ("{0}=A {1}", label, value)
    for (source, label, target) in heapGraph.GetAllEdges() do
        outStream.WriteLine ("{0:D}, {1}, A {2:D}", source, label, target)

let stackAndHeapGraphToFile (varStack : VarStack) (heapGraph : Graph<bigint, HeapLabel>) (outFilePath : string) =
    use outStream = new System.IO.StreamWriter(IOUtils.GetOutStream outFilePath)
    stackAndHeapGraphToStream varStack heapGraph outStream

let fileToStackAndHeapGraph (inFilePath : string) =
    use inStream = new System.IO.StreamReader(IOUtils.GetInStream inFilePath)
    let inFileInfo = System.IO.FileInfo inFilePath
    let varStackInfo = ref []
    let heapGraph = new MutableGraph<bigint, HeapLabel>()
    while not inStream.EndOfStream do
        let line = inStream.ReadLine()
        if line.Contains "=" then
            let lineSplit = line.Split '='
            if lineSplit.Length > 2 then
                failwith (sprintf "Variable line in '%s' with unexpected format:\n  '%s'" inFileInfo.Name line)
            else
                varStackInfo := (lineSplit.[0], Value.FromString lineSplit.[1]) :: !varStackInfo
        else if line.Contains "," then
            let lineSplit = line.Split ','
            if lineSplit.Length > 3 then
                failwith (sprintf "Heap edge line in '%s' with unexpected format:\n  '%s'" inFileInfo.Name line)
            else
                let targetVal =
                    match Value.FromString lineSplit.[2] with
                    | ValAddr a -> a
                    | _ -> failwithf "Target value is not address in '%s': Not supported." inFileInfo.Name
                let edgeLabel = HeapLabel.FromString lineSplit.[1]
                //Only add addr edges to graph:
                heapGraph.AddEdge (System.Numerics.BigInteger.Parse lineSplit.[0]) edgeLabel targetVal
        else
            failwith (sprintf "Line in '%s' with unexpected format:\n  '%s'" inFileInfo.Name line)
    let varStack = VarStack.empty (List.map fst !varStackInfo)
    List.iter (fun (varName, varVal) -> varStack.Set varName varVal) !varStackInfo

    (varStack, heapGraph :> Graph<bigint, HeapLabel>)