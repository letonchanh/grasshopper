module GraphExport
open Utils
open SepLogic

let inline GetExprValue (varEnvironment : Features.VarEnvironment) (expr : SepLogic.Expr) =
    match expr with
    | Nil -> State.ValAddr bigint.Zero
    | Var varName ->
        match Map.tryFind varName varEnvironment with
        | None -> State.ValAddr bigint.Zero //Warn?
        | Some v -> v

let private ComputeNodesCoveredByPredicate (graph : AnnotatedGraph) (pred : SepLogic.Predicate) (definedAddress : State.Value) (endAddresses : bigint seq) (oldVarEnv : Features.VarEnvironment) (subheapStartToExVarsVals : ListDictionary<State.Addr, State.Addr>) =
    //For example for lists, we want to follow the "1" pointer, for trees, we follow the "1" and "2" pointers, ...
    let definedAddress =
        match definedAddress with
        | State.ValAddr d -> d
        | _ -> failwith "Unexpected non-address value at predicate root"
    let mutable stack = [definedAddress]

    let covered = System.Collections.Generic.HashSet()
    let mutable newVarEnvs = []
    let endAddresses = System.Collections.Generic.HashSet(endAddresses)
    while not (List.isEmpty stack) do
        let curAddress = List.head stack
        stack <- List.tail stack

        if (not (endAddresses.Contains curAddress) || definedAddress = curAddress) then
            //Hack, as we are not distinguishing empty from non-empty list segments...
            let mutable goOn = true
            let outEdges = graph.BackingGraph.GetOutEdges curAddress
            if endAddresses.Contains curAddress && definedAddress = curAddress && pred.PredicateName = SepLogic.List then //Go one step, look if we can still go back to definedAddress. Then it's probably a cycle...
                let succs = Seq.filter (fst >> HeapLabel.IsDataField >> not) outEdges |> Seq.map snd
                goOn <- succs |> Seq.exists (fun succ -> (graph.GetReachableWithoutForbidden succ []).Contains curAddress)
            if goOn && covered.Add curAddress && outEdges.Count > 0 then
                let (valueEdges, recursiveEdges) = Seq.partition (fst >> HeapLabel.IsDataField) outEdges
                match pred.PredicateName with
                | SepLogic.List ->
                    stack <- (Seq.map snd recursiveEdges |> List.ofSeq) @ stack
                    match pred.TypeParameter with
                    | None -> ()
                    | Some f ->
                        let lambdaBoundVars = [f.FreeVars.Item 2]
                        let subheapStart = valueEdges |> List.head |> snd
                        let lambdaBindings = Seq.zip lambdaBoundVars [State.ValAddr subheapStart]
                        let exBindings = Seq.zip f.ExVars (subheapStartToExVarsVals.[subheapStart] |> Seq.map State.ValAddr)
                        let newVarEnv = Map.union oldVarEnv (Map.ofSeq (Seq.append lambdaBindings exBindings))
                        newVarEnvs <- newVarEnv :: newVarEnvs 
                | SepLogic.Tree ->
                    stack <- (Seq.map snd recursiveEdges |> List.ofSeq) @ stack
                    match pred.TypeParameter with
                    | None -> ()
                    | Some f ->
                        let lambdaBoundVars = [f.FreeVars.Item 1]
                        let subheapStart = valueEdges |> List.head |> snd
                        let lambdaBindings = Seq.zip lambdaBoundVars [State.ValAddr subheapStart]
                        let exBindings = Seq.zip f.ExVars (subheapStartToExVarsVals.[subheapStart] |> Seq.map State.ValAddr)
                        let newVarEnv = Map.union oldVarEnv (Map.ofSeq (Seq.append lambdaBindings exBindings))
                        newVarEnvs <- newVarEnv :: newVarEnvs 
    covered.Remove(bigint.Zero) |> ignore
    (newVarEnvs, covered)

let private ComputeExplainedNodes (graph : AnnotatedGraph) (varEnv : Features.VarEnvironment) (pred : SepLogic.Predicate) (subheapStartToExVarsVals : ListDictionary<State.Addr, State.Addr>) =
    let definedValue = GetExprValue varEnv (pred.Arguments.[0])
    match pred.PredicateName with
    | SepLogic.List ->
        let endValue = 
            match GetExprValue varEnv (pred.Arguments.[1]) with
            | State.ValAddr e -> [e]
            | _ -> failwith "Unexpected non-address value at predicate end" //[]
        ComputeNodesCoveredByPredicate graph pred definedValue endValue varEnv subheapStartToExVarsVals
    | SepLogic.Tree ->
        ComputeNodesCoveredByPredicate graph pred definedValue [] varEnv subheapStartToExVarsVals

type DataWriter = Stream of (System.IO.TextWriter -> unit) | String of string

let WriteToZip (zipArchive : System.IO.Compression.ZipArchive) (pathAndWriters : (string * DataWriter) list) =
    lock zipArchive
        (fun _ ->
            for (relativePath, writer) in pathAndWriters do
                use stream = new System.IO.StreamWriter(zipArchive.CreateEntry(relativePath).Open())
                match writer with
                | Stream f -> f stream
                | String s -> stream.WriteLine s
                stream.Close())

let WriteData zipArchive baseDirPath id step (output : string) preAnnotatedNodes postAnnotatedNodes =
    let writeAnnotatedNodes annotatedNodes (stream : System.IO.TextWriter) =
        let b2i b = if b then 1 else 0
        for (node, isNamed, isDefining, isExplained) in annotatedNodes do
            stream.WriteLine("{0} = ({1}, {2}, {3})", node, b2i isNamed, b2i isDefining, b2i isExplained)

    WriteToZip zipArchive
        [ (System.IO.Path.Combine(baseDirPath, sprintf "%sstep-%i-annotations-before.txt" id step),
           Stream (writeAnnotatedNodes preAnnotatedNodes))
        ; (System.IO.Path.Combine(baseDirPath, sprintf "%sstep-%i-annotations-after.txt" id step),
           Stream (writeAnnotatedNodes postAnnotatedNodes))
        ; (System.IO.Path.Combine(baseDirPath, sprintf "%sstep-%i-output.txt" id step),
           String output) ]

let ExtractAnnotationSteps zipArchive (dataType : IOUtils.DataSetType) formulaId graphId (formula : SepLogic.SymHeap) (state : State.State) (exVarToVal : Map<SepLogic.TypedVar, bigint>) (subheapStartToExVarsVals : ListDictionary<State.Addr, State.Addr>) =
    //Basic stuff, write out the observed graph:
    let graph = AnnotatedGraph (state.asGraph()) 
    let baseDirPath = System.IO.Path.Combine(dataType.ToString(), sprintf "formula-%i" formulaId, sprintf "graph-%i" graphId)
    let stackVars = state.varStack |> Seq.map fst |> Array.ofSeq |> Array.sort
    WriteToZip zipArchive
        [ (System.IO.Path.Combine(baseDirPath, "graph.txt"),
           Stream <| State.stackAndHeapGraphToStream state.varStack graph.BackingGraph) 
        ; (System.IO.Path.Combine(baseDirPath, "node-order.txt"),
           Stream <| (fun orderStream -> Array.iter (fun id -> fprintfn orderStream "%s" ((state.varStack.Get id).ToString())) stackVars))           
        ]


    /// The nodes that have been explained so far
    let explainedNodes = System.Collections.Generic.HashSet()
    /// The nodes that we have defined so far
    let definingNodes = System.Collections.Generic.HashSet()
    /// The nodes that carry names
    let namedNodes = System.Collections.Generic.HashSet(state.varStack |> Seq.collect (function | (_, State.ValAddr a) -> [a] | (_, State.ValInt _) -> []))

    (* Plan:
     *  (1) (Sub)formulas get IDs, so we have 1: ls(x, y, <2>) * ls(y, z, <3>)
     *  (2) Steps are relative to IDs, so we have step 1-1: ls(x, y, <2>), 1-2: ls(y, z, <3>), 2-1: ...
     *  (3) Existentials are now mapped to lists of node IDs (for subheaps)
     *  (4) Add "active" bit to graph annotations whenever we look at subheap, for all starts in parallel
     *  (5) Restrict to formulas where subheaps are nicely separated / don't interact with top-level structure
     *)

    //KnuthShuffle rng varIdentifiers //Give the identifiers a good shake

    let allNodes = graph.BackingGraph.GetNodes() |> Array.ofSeq
    Array.sortInPlace allNodes
    let computeAnnotations () =
        allNodes |> Array.map (fun n -> (n, namedNodes.Contains n, definingNodes.Contains n, explainedNodes.Contains n))


    let subFormulaCounter = ref 1
    let rec handleFormula (formulaId : string) (formula : SepLogic.SymHeap) (varEnvs : Features.VarEnvironment list) (varsToConsider : SepLogic.TypedVar seq) =
        let idToDefPred = formula.Predicates |> Seq.map (fun (p : SepLogic.Predicate) -> match p.Arguments.Head with | SepLogic.Var v -> (v, p) | _ -> failwith "!?") |> Map.ofSeq

        WriteToZip zipArchive
            [ (System.IO.Path.Combine(baseDirPath, formulaId + "existentials.txt"),
               Stream (fun exStream -> 
                            for exId in formula.ExVars do
                                let exValueStr = varEnvs |> Seq.map (fun varEnv -> (GetExprValue varEnv (SepLogic.Var exId)).ToString()) |> String.concat ","
                                fprintfn exStream "%s=%s" (exId.ToString()) exValueStr))
            ; (System.IO.Path.Combine(baseDirPath, formulaId + "variables.txt"),
               Stream (fun exStream -> 
                            for var in varsToConsider |> Seq.sort do
                                let varValueStr = varEnvs |> Seq.map (fun varEnv -> (GetExprValue varEnv (SepLogic.Var var)).ToString()) |> String.concat ","
                                fprintfn exStream "%s=%s" (var.ToString()) varValueStr))
            ; (System.IO.Path.Combine(baseDirPath, formulaId + "formula.txt"),
               String (formula.ToString()))
            ]
        let mutable step = 1
        for id in varsToConsider |> Seq.sort do
            let preAnnotations = computeAnnotations()
            match Map.tryFind id idToDefPred with
            | None ->
                WriteData zipArchive baseDirPath formulaId step (sprintf "none %s" (id.ToString())) preAnnotations preAnnotations
            | Some pred ->
                let predType = pred.PredicateName
                let arguments = pred.Arguments
                let mutable newEnvs = []
                for varEnv in varEnvs do
                    //if (GetExprValue varEnv (SepLogic.Var id)) = State.ValAddr bigint.Zero then System.Diagnostics.Debugger.Launch() |> ignore
                    let (localNewEnvs, localExplainedNodes) = ComputeExplainedNodes graph varEnv pred subheapStartToExVarsVals
                    explainedNodes.AddAll localExplainedNodes
                    let definedNode =
                        match Map.FindWithDefault id (State.ValAddr bigint.Zero) varEnv with
                        | State.ValAddr a -> a
                        | _ -> failwith "Non-address value defined"
                    definingNodes.Add definedNode |> ignore
                    newEnvs <- localNewEnvs @ newEnvs
                let postAnnotations = computeAnnotations()

                if List.length newEnvs > 0 then //Yay, recurse:
                    let newId = sprintf "%s%i-" formulaId !subFormulaCounter
                    subFormulaCounter := !subFormulaCounter + 1
                    let output = sprintf "%s(%s, %s)" (predType.ToString()) (String.concat ", " (List.map (fun e -> e.ToString()) arguments)) newId
                    WriteData zipArchive baseDirPath formulaId step output preAnnotations postAnnotations
                    let newVars = (List.head newEnvs).Keys |> Seq.filter (fun v -> not(Seq.contains v varsToConsider))
                    handleFormula newId pred.TypeParameter.Value newEnvs newVars
                else
                    let output = sprintf "%s(%s, empty)" (predType.ToString()) (String.concat ", " (List.map (fun e -> e.ToString()) arguments))
                    WriteData zipArchive baseDirPath formulaId step output preAnnotations postAnnotations

            step <- step + 1

    let typedVarStack = state.varStack |> Seq.map (function | (v, State.ValAddr a) -> (SepLogic.VarAddr v, State.ValAddr a) | (v, State.ValInt i) -> (SepLogic.VarInt v, State.ValInt i)) |> Map.ofSeq
    let typedExVarToVal = exVarToVal.Items |> Seq.map (function | (SepLogic.VarAddr varname, a) -> (SepLogic.VarAddr varname, State.ValAddr a) | (SepLogic.VarInt varname, i) -> (SepLogic.VarInt varname, State.ValInt i)) |> Map.ofSeq
    let varEnv = Map.union typedVarStack typedExVarToVal
    handleFormula "formula-" formula [varEnv] varEnv.Keys