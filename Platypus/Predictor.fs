module Predictor

open System.Diagnostics;

open Utils
open SyntaxTree
open Features
open DataSet
open MLWrapper

/// Given an array of probabilities, picks an index (of a probability) that we want to use.
let private ChooseIndex randomSelection (prng : System.Random) probabilities =
    if randomSelection then //If we want more than one prediction, pick a random one
        let cumulativeProbabilities = probabilities |> Array.scan (+) 0.
        let rn = (prng.NextDouble())*cumulativeProbabilities.[cumulativeProbabilities.Length - 1]
        let pickedIndex = (cumulativeProbabilities |> Array.findIndex (fun e -> e >= rn)) - 1
        max 0 pickedIndex
    else
        probabilities |> Array.mapi (fun i x -> i, x) |> Array.maxBy snd |> fst

let inline private pairAdd ((a1, a2) : ('T1 * 'T2) when 'T1 : (static member (+) : 'T1 * 'T1 -> 'T1)
                                                    and 'T2 : (static member (+) : 'T2 * 'T2 -> 'T2))
                           ((b1, b2) : ('T1 * 'T2)) =
    (a1 + b1, a2 + b2)
type PredictionEvaluationInformation(maxNumberOfPredictions : int) =
    let mutable observedTestCounter = 0
    let mutable greedyPredictionCorrectCounter = 0
    let mutable correctAtKCounters = [for _ in 1 .. maxNumberOfPredictions -> 0]
    let mutable rng = System.Random(42)
    let nodeTypeCorrectCounters = System.Collections.Generic.Dictionary<NodeType, int * int>()
    let formulaPredictionCorrectCounters = System.Collections.Generic.Dictionary<int, int * int>()

    member __.ObservedTestCounter with get () = observedTestCounter
    member __.CorrectAtKCounters with get () = correctAtKCounters
    member __.GreedyPredictionCorrectCounter with get () = greedyPredictionCorrectCounter
    member __.RNG
        with get () = rng
        and  set r = rng <- r

    member private __.NodeTypeCorrectCounters with get () = nodeTypeCorrectCounters
    member private __.FormulaPredictionCorrectCounters with get () = formulaPredictionCorrectCounters

    member __.NoteResult (formulaId : int) (atLeastOneCorrectPrediction : bool) (greedyPredictionCorrect : bool) (correctAtIndexList : int list) =
        observedTestCounter <- observedTestCounter + 1

        if greedyPredictionCorrect then
            greedyPredictionCorrectCounter <- greedyPredictionCorrectCounter + 1

        let toAdd = if atLeastOneCorrectPrediction then (1, 0) else (0, 1)
        let oldCounters = formulaPredictionCorrectCounters.GetWithDefault formulaId (0, 0)
        formulaPredictionCorrectCounters.[formulaId] <- pairAdd oldCounters toAdd

        correctAtKCounters <-
            correctAtIndexList
            |> List.scan (+) 0 //counting the number of correct predictions after i trees (sum should be 1)
            |> List.map (fun e -> if e > 0 then 1 else 0) // Normalization needed: Different trees might end up being the same after canonicalization
            |> List.tail //drop index 0, because it's boring
            |> List.map2 (+) correctAtKCounters //Store away with older results

    member __.NoteNodeTypePredictionResult counterType isCorrect =
        let toAdd = if isCorrect then (1, 0) else (0, 1)
        let oldCounters = nodeTypeCorrectCounters.GetWithDefault counterType (0, 0)
        nodeTypeCorrectCounters.[counterType] <- pairAdd oldCounters toAdd

    member __.KnownNodeTypeCounters
        with get () = nodeTypeCorrectCounters.Keys

    member __.NodeTypeCounter
        with get counterType =
            nodeTypeCorrectCounters.GetWithDefault counterType (0, 0)

    member __.IncludeInformation (other : PredictionEvaluationInformation) =
        observedTestCounter <- observedTestCounter + other.ObservedTestCounter
        correctAtKCounters <- List.map2 (+) correctAtKCounters other.CorrectAtKCounters
        greedyPredictionCorrectCounter <- greedyPredictionCorrectCounter + other.GreedyPredictionCorrectCounter

        for KeyValue(formulaId, otherCounterPair) in other.FormulaPredictionCorrectCounters do
            match formulaPredictionCorrectCounters.TryGetValue formulaId with
            | (true, counterPair) -> formulaPredictionCorrectCounters.[formulaId] <- pairAdd otherCounterPair counterPair
            | (false, _)          -> formulaPredictionCorrectCounters.[formulaId] <- otherCounterPair

        for KeyValue(counter, otherCounterPair) in other.NodeTypeCorrectCounters do
            match nodeTypeCorrectCounters.TryGetValue counter with
            | (true, counterPair) -> nodeTypeCorrectCounters.[counter] <- pairAdd otherCounterPair counterPair
            | (false, _)          -> nodeTypeCorrectCounters.[counter] <- otherCounterPair

    member __.PrintSummary (stream : System.IO.StreamWriter) =
        fprintfn stream "%s\nPrecision per formula:" SepLine
        for KeyValue(formulaId, (correct, incorrect)) in formulaPredictionCorrectCounters |> Seq.sortBy (function KeyValue(_, (_, incorrect)) -> incorrect) do
            fprintfn stream "  %5i: %3i correct, %3i incorrect (acc %3.2f)"
                formulaId correct incorrect (float correct / float (correct + incorrect))

        fprintfn stream "%s\nCorrectly predicted examples: %i / Total number of test examples: %i" SepLine (List.head correctAtKCounters) observedTestCounter
        let precisionAtK = correctAtKCounters |> List.mapi (fun i e -> (i + 1, (float e) / (float observedTestCounter)))
        for (k, precision) in precisionAtK do
            fprintfn stream " Precision @ %i: %.6f" k precision
        fprintfn stream "Greedy precision: %.6f" ((float greedyPredictionCorrectCounter)/(float observedTestCounter))

        for KeyValue(nodeType, (correctPredictions, incorrectPredictions)) in nodeTypeCorrectCounters do
            let totalPredictions = correctPredictions + incorrectPredictions
            fprintfn stream "Precision for %s: % 3.2f%% (%i correct, %i incorrect)"
                (nodeType.ToString()) ((float correctPredictions)/(float totalPredictions) * 100.) correctPredictions incorrectPredictions

/// <summary>
/// Predicts (or evaluates the probability of) the occurrence of an existentially
/// quantified variable.
/// </summary>
/// <param name="mlwrapper">The wrapper around all the ML components.</param>
/// <param name="subHeapStartsExistentialsAndEnvironment">
///  The observed heap / variable data. Four-tuples:
///    - The "outer" environment
///    - The "inner" environment (i.e., in case of a subheap in a data structure
///      one where lambda-bound variables are set). We need this to construct a
///      result later on and just loop it through.
///    - The "roots" of the considered heap
///    - Optionally, the actually appearing existentials
/// </param>
/// <param name="doSampling">Triggers actual sampling from the induced
///  distribution, instead greedily picking the option with the highest
///  probability.</param>
/// <param name="pnrg">The RNG, passed around to have deterministic outcomes.</param>
/// <param name="evalInfo">The container for evaluation information.</param>
let private PredictExistentiallyQuantified
        (mlwrapper : ModelWrapper)
        (heapStartsExistentialsAndEnvironments : (Environment * Environment * bigint seq * bigint list option) list)
        (doSampling : bool)
        (prng : System.Random)
        (remainingAllowedProductions : int ref)
        (evalInfo : PredictionEvaluationInformation option)
        (numOfExistentialsToPick : int option)  =

    //Each call of this function either predicts a new existential, or decides that we are done and returns.
    let logProb = ref 0.
    let rec predictExistentiallyQuantified (subheapInformation : (Environment * bigint seq * bigint list * bigint list * bigint list option) list) (numOfExistentialsToPick : int option) debug =
        (* First, extract feature and score all addresses accross all heaps.
         * We use the following following notation:
         *  s^H_a: Score of address a in heap H
         *  z = \prod_{considered subheap H} \sum_{addr a in H} exp s^H_a
         *  s_max = \sum_{considered subheap H} \max_{addr a in H} s^H_a
         * For a given sequence of addresses a_1 ... a_n, with a_i in heap H_i,
         * the probability of picking that address combination is
         *       exp(\sum_{1 <= i <= n} s^{H_i}_{a_i}) / (1+z)
         * The probability of not picking any existential is 1 / (1+z), and the
         * probability of the most likely address combination is exp(s_max) / (1+z)
         *)
        let minSubheapSize = ref System.Int32.MaxValue
        let z = ref 1.
        let s_max = ref 0.
        let scoredAddressesWithSubheapInformation =
            [
                for ((heapGraph, _), subheapStarts, namedAddresses, chosenExistentials, _) as subheapInfo in subheapInformation do
                    let addressesWithFeatures = Features.AddressesToExistentialsDataSet heapGraph.Graph subheapStarts (chosenExistentials @ namedAddresses)
                    let scoredAddresses = mlwrapper.ExistentialScores addressesWithFeatures
                    minSubheapSize := min !minSubheapSize scoredAddresses.Length
                    z := !z * (scoredAddresses |> Seq.sumBy (snd >> exp))
                    s_max := !s_max + (if scoredAddresses.Length > 0 then scoredAddresses |> Seq.maxBy snd |> snd else 0.)
                    yield (scoredAddresses, subheapInfo)
            ]
        let logProbOfNotPicking = - log(1. + !z) // = log(1/(1+z))
        let logProbOfMaxPick = !s_max - log(1. + !z)

        //Three cases: Evaluation, or prediction with greedy choice or sampling. We handle the latter two together.
        match numOfExistentialsToPick with
        | Some numOfExistentialsToPick ->
            Debug.Assert(evalInfo.IsSome, "evaluation requires information container")
            if numOfExistentialsToPick <= 0 then //Case "we shouldn't pick one"
                logProb := !logProb + logProbOfNotPicking
                evalInfo.Value.NoteNodeTypePredictionResult ExistentialBinding (logProbOfNotPicking >= logProbOfMaxPick)
                (!logProb, List.map (fun (_, (newEnv, _, _, chosenExistentials, _)) -> (newEnv, chosenExistentials)) scoredAddressesWithSubheapInformation)
            else
                //Compute probability of pick:
                let sumOfScoresOfPick = ref 0.
                let newData =
                    [
                        for (scoredAddresses, (newEnv, subheapStarts, namedAddresses, chosenExistentials, optGroundtruthExistentials)) in scoredAddressesWithSubheapInformation do
                            let (scoreOfPickedAddress, pickedAddress, optRemainingGroundtruth) =
                                //Two cases: We know ground truth; or we just pick the most likely
                                match optGroundtruthExistentials with
                                | Some (pickedAddress::remainingGroundtruth) ->
                                    let pickedAddressScore = scoredAddresses |> Seq.find (fst >> (=) pickedAddress) |> snd
                                    (pickedAddressScore, pickedAddress, Some remainingGroundtruth)
                                | Some [] //We've run out of things that should be picked (or never them), so now we just pick the most likely one
                                | None ->
                                    let (pickedAddress, pickedAddressScore) = Seq.maxBy snd scoredAddresses
                                    (pickedAddressScore, pickedAddress, None)
                            sumOfScoresOfPick := !sumOfScoresOfPick + scoreOfPickedAddress
                            yield (newEnv, subheapStarts, namedAddresses, pickedAddress::chosenExistentials, optRemainingGroundtruth)
                    ]
                let logProbOfPick = !sumOfScoresOfPick - log(1. + !z)
                logProb := !logProb + logProbOfPick
                evalInfo.Value.NoteNodeTypePredictionResult ExistentialBinding (logProbOfPick > logProbOfMaxPick && logProbOfPick > logProbOfNotPicking)
                predictExistentiallyQuantified newData (Some (numOfExistentialsToPick - 1)) debug
        | None ->
            if doSampling then //Sampling case
                let probOfPickingOne = 1. - exp(logProbOfNotPicking)
                if debug then
                    printfn " Probability of predicting an existential quantifier:"
                    printfn " {p=%.4f} Ex var. formula" (probOfPickingOne)
                    printfn " {p=%.4f} formula\n" (1. - probOfPickingOne)
                if !remainingAllowedProductions > 0 && !minSubheapSize > 0 && prng.NextDouble() <= probOfPickingOne then
                    //Now choose one from each subheap:
                    let sumOfScoresOfPick = ref 0.
                    let newData =
                        [
                            for (scoredAddresses, (newEnv, subheapStarts, namedAddresses, chosenExistentials, _)) in scoredAddressesWithSubheapInformation do
                                let totalExpScore = scoredAddresses |> Seq.sumBy (snd >> exp)
                                let cumulativeProbabilitiesWithAddresses =
                                    scoredAddresses |> Array.scan (fun (_, prefixS) (a, s) -> (a, prefixS + (exp s)/totalExpScore)) (bigint.Zero, 0.)
                                let rn = (prng.NextDouble()) * snd cumulativeProbabilitiesWithAddresses.[cumulativeProbabilitiesWithAddresses.Length - 1]
                                let pickedIndex = (cumulativeProbabilitiesWithAddresses |> Array.findIndex (fun (_, prob) -> prob >= rn)) - 1
                                let pickedIndex = max (min pickedIndex (scoredAddresses.Length - 1)) 0
                                sumOfScoresOfPick := !sumOfScoresOfPick + (snd scoredAddresses.[pickedIndex])
                                let chosenExistential = fst scoredAddresses.[pickedIndex]
                                yield (newEnv, subheapStarts, namedAddresses, chosenExistential::chosenExistentials, None)
                        ]
                    logProb := !logProb + (!sumOfScoresOfPick - log(1. + !z)) // = ... + (log(exp(\sum_{1 <= i <= n} s^{H_i}_{a_i}) / (1+z)))
                    remainingAllowedProductions := !remainingAllowedProductions - 1
                    predictExistentiallyQuantified newData None debug
                else
                    logProb := !logProb + logProbOfNotPicking
                    (!logProb, List.map (fun (_, (newEnv, _, _, chosenExistentials, _)) -> (newEnv, chosenExistentials)) scoredAddressesWithSubheapInformation)
            else //Greedy pick case:
                if debug then
                    let probOfPickingOne = 1. - exp(logProbOfNotPicking)
                    printfn " Probability of predicting an existential quantifier:"
                    printfn " {p=%.4f} Ex var. formula" (probOfPickingOne)
                    printfn " {p=%.4f} formula\n" (1. - probOfPickingOne)
                if !remainingAllowedProductions > 0 && !minSubheapSize > 0 && logProbOfMaxPick > logProbOfNotPicking then
                    let newData =
                        scoredAddressesWithSubheapInformation
                        |> List.map
                            (fun (scoredAddresses, (newEnv, subheapStarts, namedAddresses, chosenExistentials, _)) ->
                                let chosenExistential = scoredAddresses |> Seq.maxBy snd |> fst
                                (newEnv, subheapStarts, namedAddresses, chosenExistential::chosenExistentials, None))
                    logProb := !logProb + logProbOfMaxPick
                    remainingAllowedProductions := !remainingAllowedProductions - 1
                    predictExistentiallyQuantified newData None debug
                else
                    logProb := !logProb + logProbOfNotPicking
                    (!logProb, List.map (fun (_, (newEnv, _, _, chosenExistentials, _)) -> (newEnv, chosenExistentials)) scoredAddressesWithSubheapInformation)

    /// 4-tuples: Environment, addresses that are roots of the considered subheap, addresses that already have names, addresses that we pick as existentials, possible ground truth values
    let subheapInformation : (Environment * bigint seq * bigint list * bigint list * bigint list option) list =
        heapStartsExistentialsAndEnvironments
        |> List.map
            (fun ((_, oldVarEnv), newEnv, subheapStarts, optExistentials) ->
                (newEnv, subheapStarts, (Features.restrictToAddrs oldVarEnv).Values |> List.ofSeq, [], optExistentials))
    predictExistentiallyQuantified subheapInformation numOfExistentialsToPick

/// Compute fresh variable bindings under the assumptions made in the prediction of this syntax tree.
/// For this, we assume node to be a node pointing to a symheap in a syntax tree. If it is nested in a
/// \lambda expression, we will need to look at many subheaps, instead of just one. For this, we
/// compute all of these subheaps, and create fresh variable bindings in which the lambda-bound
/// variables are instantiated accordingly.
let private ComputeSubheapStartsAndNewEnvironments (syntaxTree : SyntaxTree.SyntaxTree) curNode (environments : Environment list) : (bigint seq * Environment * Environment) list =
    match syntaxTree.GetParent curNode with
    | Some parentNode ->
        match parentNode.NodeType with
        | TypedLambdaBinding definedPredicate ->
            let lambdaBoundVariables =
                syntaxTree.GetChildren parentNode
                |> Seq.filter (fun (n : SyntaxTree.Node) -> n.NodeType.IsVar)
                |> Seq.map (fun node -> SepLogic.VarAddr (syntaxTree.GetNameFromExpressionNode node))
            let lambdaBoundVariablesCount = Seq.length lambdaBoundVariables

            let typedHeapletNode = (syntaxTree.GetParent (syntaxTree.GetParent parentNode).Value).Value
            let typedHeapletArguments = syntaxTree.GetTypedHeapletArguments typedHeapletNode
            let argumentVarNames = Seq.map syntaxTree.GetNameFromExpressionNode typedHeapletArguments
            let computeEnvironmentsForSubheaps ((heapGraph, varEnv) as env : Environment) =
                let argumentVarAddrs = Seq.map (GetAddrOfVarName varEnv) argumentVarNames
                let addLambdaInstantiations varEnv lambdaInstantiation =
                    let lenDiff = lambdaBoundVariablesCount - Seq.length lambdaInstantiation
                    Seq.fold2 (fun varEnv variable value -> Map.add variable (State.ValAddr value) varEnv)
                        varEnv lambdaBoundVariables (Seq.take lambdaBoundVariablesCount (Seq.append lambdaInstantiation (Seq.repeat lenDiff bigint.Zero)))
                let definedVar = Seq.head argumentVarNames
                let otherAddrs =
                    varEnv
                    |> Seq.filter (fun t -> match t.Key with | SepLogic.VarAddr n | SepLogic.VarInt n -> n <> definedVar)
                    |> Seq.map (fun t -> t.Value)
                    |> Value.valSeqToAddrSeq
                Features.GetSubHeapsOfPredicate heapGraph.Graph definedPredicate argumentVarAddrs otherAddrs
                |> List.map (fun (s, lambdaInstantiation) -> (s, env, (heapGraph, addLambdaInstantiations varEnv lambdaInstantiation)))
            List.collect computeEnvironmentsForSubheaps environments
        | _ -> List.map (fun env -> (Seq.empty, env, env)) environments
    | None -> List.map (fun (((_, varEnv) : Environment) as env) -> ((State.Value.valSeqToAddrSeq varEnv.Values), env, env)) environments

let private GetFeaturesForProductionStep contextFeatures heapGraphFeatures (environments : Environment list) stackVariables (syntaxTree : SyntaxTree) (curNode : Node) =
    match curNode.NodeType with
    | LambdaBinding ->
        let predicateHeapletNode = (syntaxTree.GetParent curNode).Value
        let predicateType =
            match predicateHeapletNode.NodeType with
            | TypedHeaplet typ -> typ
            | _ -> failwith "Can't identify type of heaplet"
        let predicateArguments =
            syntaxTree.GetChildren predicateHeapletNode
            |> Seq.filter (fun n -> n.NodeType.IsExpr)
            |> Seq.map syntaxTree.GetNameFromExpressionNode
        let definedVar = Seq.head predicateArguments
        let environmentsWithSubheapStarts =
            environments
            |> List.collect
                (fun (heapGraph, varEnv) ->
                    let predicateArgumentAddrs = Seq.map (GetAddrOfVarName varEnv) predicateArguments
                    let otherAddrs =
                        varEnv
                        |> Seq.filter (fun t -> match t.Key with | SepLogic.VarAddr n | SepLogic.VarInt n -> n <> definedVar)
                        |> Seq.map (fun t -> t.Value)
                        |> Value.valSeqToAddrSeq
                    Features.GetSubHeapsOfPredicate heapGraph.Graph predicateType predicateArgumentAddrs otherAddrs
                    |> List.map (fun (subheapStart, _) -> ((heapGraph, varEnv), subheapStart)))
        Features.ComputeLambdaFeatures environmentsWithSubheapStarts syntaxTree curNode
    | Heaplets ->
        Features.ComputeHeapletsFeatures environments stackVariables syntaxTree curNode
    | Heaplet ->
        Features.ComputeHeapletFeatures environments stackVariables syntaxTree curNode
    | _ ->
        SparseFeatures.union heapGraphFeatures contextFeatures

let private addExprNode (syntaxTree : SyntaxTree.SyntaxTree) parentNode (e, field) =
    let exprNode = Node Expression
    syntaxTree.AddEdge parentNode exprNode
    match e with
    | SepLogic.Nil   -> syntaxTree.AddEdge exprNode (Node (ExpressionId "nil"))
    | SepLogic.Var v ->
        syntaxTree.AddEdge exprNode (Node (ExpressionId v.Name))
        match field with
        | None -> ()
        | Some field ->
            syntaxTree.AddEdge exprNode (Node SyntaxTree.FieldDeref)
            syntaxTree.AddEdge exprNode (Node (SyntaxTree.FieldId field))


let predictPureFormula (syntaxTree : SyntaxTree) (pureFormulaNode : Node) (enclosingVarEnvs : Environment list) (newVarEnvs : Environment list) =
    //First, get variables that we didn't have before:
    let oldVariables =
        match enclosingVarEnvs with
        | [] -> Set.empty
        | (_, enclosingVarEnv) :: _ -> // We only care about the key set, and that's the same anyway for all of them
            Set.ofSeq enclosingVarEnv.Keys
    let newVariables =
        match newVarEnvs with
        | [] -> Set.empty
        | (_, newVarEnv) :: _ ->
            Set.ofSeq newVarEnv.Keys
    let addedVariables = Set.difference newVariables oldVariables

    let isFirst = ref true
    let addFormula relationType e1 e2 =
        if !isFirst then
            isFirst := false
        else
            syntaxTree.AddEdge pureFormulaNode (Node Conjunction)
        let relationNode = Node PureRelation
        syntaxTree.AddEdge pureFormulaNode relationNode

        addExprNode syntaxTree relationNode e1
        match relationType with
        | SepLogic.Eq -> syntaxTree.AddEdge relationNode (Node Eq)
        | SepLogic.Ne -> syntaxTree.AddEdge relationNode (Node Ne)
        addExprNode syntaxTree relationNode e2

    //First, generate all <> nil:
    for v in addedVariables do
        let mutable isAlwaysNil = true
        let mutable isNeverNil = true
        let edgeIsAlwaysNil = System.Collections.Generic.Dictionary()

        for (heapGraph, varEnv) in newVarEnvs do
            let vVal = Map.find v varEnv
            match vVal with
            | State.ValAddr vAddrVal ->
                let isNil = (vAddrVal = bigint.Zero)
                isAlwaysNil <- isAlwaysNil && isNil
                isNeverNil <- isNeverNil && not isNil
                let outEdges = heapGraph.Graph.BackingGraph.GetOutEdges vAddrVal
                for knownFieldId in Utils.KnownFieldIds do
                    let oldEqualityValue = defaultArg (edgeIsAlwaysNil.TryFind knownFieldId) true
                    let fieldEdge = Seq.tryFind (fst >> HeapLabel.GetId >> (=) knownFieldId) outEdges
                    match fieldEdge with
                    | Some (_, value) -> edgeIsAlwaysNil.[knownFieldId] <- oldEqualityValue && value = bigint.Zero
                    | None -> edgeIsAlwaysNil.[knownFieldId] <- false
            | _ ->
                isAlwaysNil <- false
                isNeverNil <- false

        if isAlwaysNil then
            addFormula SepLogic.Eq (SepLogic.Var v, None) (SepLogic.Nil, None)
        if isNeverNil then
            addFormula SepLogic.Ne (SepLogic.Var v, None) (SepLogic.Nil, None)
        for kv in edgeIsAlwaysNil |> Seq.filter (fun kv -> kv.Value) do
            let fieldName = Utils.GetFieldNameForId kv.Key
            addFormula SepLogic.Eq (SepLogic.Var v, Some fieldName) (SepLogic.Nil, None)

        //Then compare with all variables:
        for v' in newVariables do
            let mutable areAlwaysEqual = true
            let mutable areAlwaysInequal = true
            let edgeIsAlwaysEqual = System.Collections.Generic.Dictionary()
            for (heapGraph, varEnv) in newVarEnvs do
                let (vVal, v'Val) = (Map.find v varEnv, Map.find v' varEnv)
                let areEqual = (vVal = v'Val)
                areAlwaysEqual <- areAlwaysEqual && areEqual
                areAlwaysInequal <- areAlwaysInequal && not areEqual

                match (vVal, v'Val) with
                | (State.ValAddr vAddrVal, State.ValAddr v'AddrVal) ->
                    let outEdges = heapGraph.Graph.BackingGraph.GetOutEdges vAddrVal
                    for knownFieldId in Utils.KnownFieldIds do
                        let oldEqualityValue = defaultArg (edgeIsAlwaysEqual.TryFind knownFieldId) true
                        let fieldEdge = Seq.tryFind (fst >> HeapLabel.GetId >> (=) knownFieldId) outEdges
                        match fieldEdge with
                        | Some (_, value) -> edgeIsAlwaysEqual.[knownFieldId] <- oldEqualityValue && value = v'AddrVal
                        | None -> edgeIsAlwaysEqual.[knownFieldId] <- false
                | _ -> ()
            if v.Name.CompareTo(v'.Name) < 0 then
                if areAlwaysEqual then
                    addFormula SepLogic.Eq (SepLogic.Var v, None) (SepLogic.Var v', None)
                if areAlwaysInequal then
                    addFormula SepLogic.Ne (SepLogic.Var v, None) (SepLogic.Var v', None)
            for kv in edgeIsAlwaysEqual |> Seq.filter (fun kv -> kv.Value) do
                let fieldName = Utils.GetFieldNameForId kv.Key
                addFormula SepLogic.Eq (SepLogic.Var v, Some fieldName) (SepLogic.Var v', None)

    //Add a true if we didn't add anything:
    if !isFirst then
        syntaxTree.AddEdge pureFormulaNode (Node True)

exception TreeDerivationTooLarge of string

/// Given heap graph features, predict syntax tree of a formula describing it.
let PredictSyntaxTree (mlwrapper : ModelWrapper) (environments : Environment list) numPredictions (canonicalize : bool) (insertBtwns : bool) (debug : bool) =
    let rng = System.Random(42)
    let stackVariables = (environments |> List.head |> snd).Keys |> Seq.map (fun var -> var.Name)
    let maxNumProdAllowed = 200

    let jointHeapGraphFeatures = Features.ExtractHeapGraphFeatures environments

    /// Provides a prediction of the expansion of one "standard" non-terminal node in a syntax tree.
    /// Returns tuple of probability of the chosen production and of the children nodes created for that.
    let predictOneProduction (environments : Environment list) (syntaxTree : SyntaxTree) (curNode : Node) randomSelection contextFeatures =
        let features = GetFeaturesForProductionStep contextFeatures jointHeapGraphFeatures environments stackVariables syntaxTree curNode
        let (productions, probabilities) = mlwrapper.PredictNonterminalProductions features curNode
        let predictedLabel = ChooseIndex randomSelection rng probabilities

        // Pick predicted production to extend syntax tree:
        let chosenProd = productions.[predictedLabel]
        if debug && Array.length productions > 1 then
            printfn " Probabilities of productions for leftmost '%s' in '%s':" (curNode.ToString()) (syntaxTree.ToStringDetailed())
            printfn "  Features: %s" (features |> Seq.map (fun (feature, value) -> sprintf "%s:%.2f" feature value) |> String.concat " ")
            let chosenProdString = chosenProd.ToString()
            for (prod, prob) in Array.zip productions probabilities do
                let prodString = prod.ToString()
                let mark = if prodString = chosenProdString then "*" else " "
                printfn " %s{p=%.4f} %s" mark prob (prod.ToString())
            printfn "  Chosen production: %s\n" (productions.[predictedLabel].ToString())
        (probabilities.[predictedLabel], chosenProd)

    let varIdx = ref 1
    let freshVarNode () =
        let varNode = Node (ExpressionId ("v" + string !varIdx))
        varIdx := !varIdx + 1
        varNode

    let predictTree (initialEnvironments : Environment list) randomSelection numberOfAllowedProductions =
        let rec predictTreeStepwise (environments : Environment list) (syntaxTree : SyntaxTree) (curNode : SyntaxTree.Node) doSampling remainingAllowedProductions overallLogProb =
            if !remainingAllowedProductions <= 0 then
                raise (TreeDerivationTooLarge "The tree is too damn high! http://bit.ly/1z76tHa")
            else if curNode.NodeType.IsTerminal then
                ()
            else
                let contextFeatures = SparseFeatures()
                remainingAllowedProductions := !remainingAllowedProductions - 1
                match curNode.NodeType with
                | Expression ->
                    let expressionsWithFeatures = Features.ComputeExpressionFeatures stackVariables environments syntaxTree curNode ""
                    let exprPosId = syntaxTree.GetExprNodePosDescriptor curNode
                    let (expressions, probabilities) = mlwrapper.PredictExprProductions exprPosId expressionsWithFeatures
                    let chosenExpressionIdx = ChooseIndex doSampling rng probabilities
                    let chosenExpression = expressions.[chosenExpressionIdx]
                    overallLogProb := !overallLogProb + log(probabilities.[chosenExpressionIdx])
                    if debug then
                        printfn " Probabilities of productions of '%s' in '%s':" (curNode.ToString()) (syntaxTree.ToStringDetailed())
                        for (prod, prob) in Array.zip expressions probabilities do
                            let (_, _, features) = List.find (fun (_, expr, _) -> expr = prod) expressionsWithFeatures
                            let mark = if chosenExpression = prod then "*" else " "
                            printfn " %s{p=%.4f} %s (%s)" mark prob prod (features.ToString())
                        printfn "  Chosen production: %s\n" chosenExpression
                    syntaxTree.AddEdge curNode (Node(ExpressionId chosenExpression))
                | Symheap ->
                    //Two special things happen here:
                    // (1) We may generate many more variable bindings (each corresponding to one of the subheaps described by this symbolic heap)
                    // (2) We may also guess which addresses should get names via existential quantification
                    let newEnvironmentWithHeapRoots =
                        ComputeSubheapStartsAndNewEnvironments syntaxTree curNode environments
                        |> List.map (fun (heapRoots, oldEnv, newEnv) -> (oldEnv, newEnv, heapRoots, None))

                    //We sometimes get the case that we ended up without new environments (when we totally mispredicted the predicate). In that case, just stop here...
                    if newEnvironmentWithHeapRoots.Length = 0 then
                        let typedLambdaNode = syntaxTree.GetParent (syntaxTree.GetParent curNode).Value
                        let freshNoLambda = Node EmptyLambdaBinding
                        syntaxTree.ReplaceSubtree typedLambdaNode.Value freshNoLambda
                    else
                        let (logProb, existentialsAndVarheaps) =
                            PredictExistentiallyQuantified mlwrapper newEnvironmentWithHeapRoots doSampling rng remainingAllowedProductions None None debug
                        overallLogProb := !overallLogProb + logProb

                        //First generate new names for the chosen existentials, then build syntax tree using them:
                        let numberOfExistentials = List.length (snd <| List.head existentialsAndVarheaps)
                        let mutable intermediateNode = curNode
                        let mutable existentialVariableNames = []
                        for _ in  1 .. numberOfExistentials do
                            let quantifierNode = Node ExistentialBinding
                            syntaxTree.AddEdge intermediateNode quantifierNode

                            syntaxTree.AddEdge quantifierNode (Node Exists)
                            let varNode = Node Variable
                            syntaxTree.AddEdge quantifierNode varNode
                            let freshVarNode = freshVarNode()
                            syntaxTree.AddEdge varNode freshVarNode
                            existentialVariableNames <- (SepLogic.VarAddr (syntaxTree.GetNameFromExpressionNode varNode)) :: existentialVariableNames
                            syntaxTree.AddEdge quantifierNode (Node Period)
                            intermediateNode <- quantifierNode

                        //Add the existentials to the variable bindings:
                        let mutable newEnvironments = []
                        for ((heapGraph, varEnv), existentialAddresses) in existentialsAndVarheaps do
                            let existentialValues = Seq.map State.ValAddr existentialAddresses
                            newEnvironments <- (heapGraph, (Map.union (Map.ofSeq (Seq.zip existentialVariableNames existentialValues)) varEnv)) :: newEnvironments
                        let pureFormulaNode = Node PureFormula
                        syntaxTree.AddEdge intermediateNode pureFormulaNode
                        if (syntaxTree.GetParent curNode).IsNone then
                            predictPureFormula syntaxTree pureFormulaNode (if (syntaxTree.GetParent curNode).IsNone then [] else environments) newEnvironments
                        else
                            syntaxTree.AddEdge pureFormulaNode (Node True)
                        syntaxTree.AddEdge intermediateNode (Node Colon)
                        let heapletsNode = Node Heaplets
                        syntaxTree.AddEdge intermediateNode heapletsNode
                        predictTreeStepwise newEnvironments syntaxTree heapletsNode randomSelection remainingAllowedProductions overallLogProb
                | Variable ->
                    syntaxTree.AddEdge curNode (freshVarNode ())
                | _ ->
                    let (chosenProbability, predictedChildren) = predictOneProduction environments syntaxTree curNode randomSelection contextFeatures
                    overallLogProb := !overallLogProb + log(chosenProbability)

                    //This is needed to insert and then process them in the right order:
                    for childNodeType in predictedChildren do
                        let childNode = Node childNodeType
                        syntaxTree.AddEdge curNode childNode
                        predictTreeStepwise environments syntaxTree childNode randomSelection remainingAllowedProductions overallLogProb
        let freshSyntaxTree = SyntaxTree.Empty
        let overallProbability = ref 0.
        try
            predictTreeStepwise initialEnvironments freshSyntaxTree freshSyntaxTree.root randomSelection (ref numberOfAllowedProductions) overallProbability
            (freshSyntaxTree, exp !overallProbability)
        with
        | TreeDerivationTooLarge _ ->
            printfn "Error PredictSyntaxTree: TreeDerivationTooLarge"
            (SyntaxTree.Empty, 0.)
        | ex ->
            printfn "Error PredictSyntaxTree: %s." (ex.Message)
            (SyntaxTree.Empty, 0.)

    let getOutputString (st : SyntaxTree.SyntaxTree) =
        //Remove superfluous lseg(a, b) if we have a.next == b
        let getNextPairsFromPureFormulaNode pureFormulaNode =
            [
            let getFieldId n =
                match Node.GetNodeType n with
                | FieldId id -> id
                | _ -> failwith "No field id!"
            for relationNode in st.GetChildren pureFormulaNode |> Seq.filter (Node.GetNodeType >> (=) PureRelation) do
                let relationNodeChildren = st.GetChildren relationNode
                if relationNodeChildren.Count = 3 && Node.GetNodeType relationNodeChildren.[1] = Eq then
                    let leftArgChildren = st.GetChildren relationNodeChildren.[0]
                    let rightArgChildren = st.GetChildren relationNodeChildren.[2]
                    if leftArgChildren.Count = 3 && Node.GetNodeType leftArgChildren.[1] = FieldDeref && (getFieldId leftArgChildren.[2]).EndsWith("next") then
                        let leftArg = leftArgChildren.[0].GetNameFromExpressionId
                        let rightArg = rightArgChildren.[0].GetNameFromExpressionId
                        yield (leftArg, rightArg)
            ]

        let addVarExprNode (st : SyntaxTree.SyntaxTree) parent varName =
            let exprNode = Node Expression
            st.AddEdge parent exprNode
            st.AddEdge exprNode (Node (ExpressionId varName))

        //Replaces occurrences of ls(x, y) && x.next == y by acc(x) && x.next = y
        let rec replaceNextPairs heapletsNode nextPairs =
            let heapletsChildren = heapletsNode |> st.GetChildren

            match Seq.tryFind (Node.GetNodeType >> (=) Heaplet) heapletsChildren with
            | None -> ()
            | Some heapletChild ->
                let listChild =
                    Seq.tryFind (Node.GetNodeType >> (=) (TypedHeaplet SepLogic.List)) (st.GetChildren heapletChild)
                match listChild with
                | None -> ()
                | Some listNode ->
                    let args = st.GetChildren listNode
                    let startArg =  st.GetNameFromExpressionNode args.[2]
                    let endArg =  st.GetNameFromExpressionNode args.[4]
                    if List.contains (startArg, endArg) nextPairs then
                        let accPredNode = Node AccPred
                        st.AddEdge accPredNode (Node Acc)
                        st.AddEdge accPredNode (Node LParen)
                        addVarExprNode st accPredNode startArg
                        st.AddEdge accPredNode (Node RParen)
                        st.ReplaceSubtree heapletChild accPredNode
                replaceNextPairs (heapletsChildren |> Seq.find (Node.GetNodeType >> (=) Heaplets)) nextPairs

        // Search for pure formula node either at topmost level or after all existential bindings
        match st.GetChildrenTuple st.root with
        | [||] -> ()
        | _ ->
            let rootNode =
                let rec findFirstNonExistential node =
                    let children = st.GetChildrenTuple node
                    match children |> Array.tryFind (fun n -> n.NodeType = ExistentialBinding) with
                    | Some n -> findFirstNonExistential n
                    | None -> node
                findFirstNonExistential st.root
            let nextPairs =
                (st.GetChildren rootNode |> Seq.filter (Node.GetNodeType >> (=) PureFormula) |> Seq.head)
                |> getNextPairsFromPureFormulaNode
            replaceNextPairs (st.GetChildren rootNode |> Seq.find (fun node -> node.NodeType = Heaplets)) nextPairs

        //Try to insert "Btwn" predicates that grasshopper needs in certain corner-cases.
        //For this, look for ls(v1, v2), ls(v2, v3) in the formula. Then, if z does not occur on ls(v1, v2) in any of the samples, add Btwn(1, v1, v2, v3)

        //Step one: Extract the (v1, v2) pairs from ls(v1, v2, _) [and set flag if not all ls have a _ in the last pos]
        let isSimpleFormula = ref true
        let emptyHeapletNode = ref st.root
        let rec getListPairsFromHeapletsNode heapletsNode foundSoFar =
            let heapletsChildren = heapletsNode |> st.GetChildren

            match Seq.tryFind (Node.GetNodeType >> (=) Heaplet) heapletsChildren with
            | None ->
                //But does it continue?
                match Seq.tryFind (Node.GetNodeType >> (=) Heaplets) heapletsChildren with
                | None ->
                    emptyHeapletNode := Seq.find (Node.GetNodeType >> (=) EmptyHeaplet) heapletsChildren
                    foundSoFar
                | Some heapletsChild ->
                    getListPairsFromHeapletsNode heapletsChild foundSoFar
            | Some heapletChild ->
                let listChild =
                    Seq.tryFind (Node.GetNodeType >> (=) (TypedHeaplet SepLogic.List)) (st.GetChildren heapletChild)

                let thisHeapletRes =
                    match listChild with
                    | None -> []
                    | Some listNode ->
                        let args = st.GetChildren listNode
                        let hasEmptyLambda = args |> Seq.exists (Node.GetNodeType >> (=) EmptyLambdaBinding)
                        if not hasEmptyLambda then
                            isSimpleFormula := false
                        let argNodes =
                            args
                            |> Seq.filter (fun node -> node.NodeType = Expression)
                            |> Seq.map st.GetNameFromExpressionNode
                            |> Array.ofSeq
                        if argNodes.Length = 2 then
                            [(argNodes.[0], argNodes.[1])]
                        else
                            isSimpleFormula := false
                            []
                let foundSoFar = thisHeapletRes @ foundSoFar
                getListPairsFromHeapletsNode (heapletsChildren |> Seq.find (Node.GetNodeType >> (=) Heaplets)) foundSoFar

        let workaround() = null |> ignore // c.f. https://github.com/Microsoft/visualfsharp/issues/759
        let transitiveClosure pairs =
            let vars = List.fold (fun set (v1, v2) -> Set.add v1 (Set.add v2 set)) Set.empty pairs
            let canReach = System.Collections.Generic.Dictionary()

            for v1 in vars do
                for v2 in vars do
                    canReach.[(v1, v2)] <- false

            for v1, v2 in pairs do
                canReach.[(v1, v2)] <- true

            for k in vars do
                for i in vars do
                    for j in vars do
                        canReach.[(i, j)] <- canReach.[(i, j)] || (canReach.[(i, k)] && canReach.[(k, j)])

            vars, canReach

        if insertBtwns && not <| st.IsLeafNode st.root then
            let heapletsNode = st.GetChildren st.root |> Seq.tryFind (fun node -> node.NodeType = Heaplets)
            match heapletsNode with
            | None -> ()
            | Some heapletsNode ->
                let vars, canReach = getListPairsFromHeapletsNode heapletsNode [] |> transitiveClosure
                let vars = Set.remove "nil" vars
                if !isSimpleFormula then
                    workaround() // c.f. https://github.com/Microsoft/visualfsharp/issues/759
                    for v1 in vars do
                        workaround() // c.f. https://github.com/Microsoft/visualfsharp/issues/759
                        for v2 in vars do
                            workaround() // c.f. https://github.com/Microsoft/visualfsharp/issues/759
                            for v3 in vars do
                                if canReach.[(v1, v2)] && canReach.[(v2, v3)]  && v1 <> v2 && v2 <> v3 && v3 <> v1 then
                                    let mutable shouldInsert = true
                                    for (hG, vEnv) in environments do
                                        //Check if v3 is on path from v1 to v2. If yes, drop out:
                                        let v1Val = match Map.tryFind (SepLogic.VarAddr v1) vEnv with | Some (Value.ValAddr v) -> v | _ -> bigint.Zero
                                        let v2Val = match Map.tryFind (SepLogic.VarAddr v2) vEnv with | Some (Value.ValAddr v) -> v | _ -> bigint.Zero
                                        let v3Val = match Map.tryFind (SepLogic.VarAddr v3) vEnv with | Some (Value.ValAddr v) -> v | _ -> bigint.Zero
                                        if v1Val <> v2Val && hG.Graph.IsReachableWithoutForbidden v1Val v3Val [v2Val] (System.Collections.Generic.HashSet()) then
                                            shouldInsert <- false
                                    if shouldInsert then
                                        //Insert new heaplets thing instead of empty heaplet:
                                        let heapletsNode = Node Heaplets
                                        st.ReplaceSubtree !emptyHeapletNode heapletsNode
                                        let btwnPredNode = Node BtwnPred
                                        st.AddEdge heapletsNode btwnPredNode
                                        st.AddEdge btwnPredNode (Node Btwn)
                                        st.AddEdge btwnPredNode (Node LParen)
                                        st.AddEdge btwnPredNode (Node (StringLiteral "next"))
                                        st.AddEdge btwnPredNode (Node Comma)
                                        addVarExprNode st btwnPredNode v1
                                        st.AddEdge btwnPredNode (Node Comma)
                                        addVarExprNode st btwnPredNode v2
                                        st.AddEdge btwnPredNode (Node Comma)
                                        addVarExprNode st btwnPredNode v3
                                        st.AddEdge btwnPredNode (Node RParen)

                                        st.AddEdge heapletsNode (Node SepStar)
                                        st.AddEdge heapletsNode !emptyHeapletNode

        if canonicalize then st.ToCanonicalString() else st.ToString()

    let (greedySample, prob) = predictTree environments false maxNumProdAllowed
    let greedySampleString =
        if greedySample.IsLeafNode greedySample.root then // Empty tree
            if canonicalize then greedySample.ToCanonicalString() else greedySample.ToString()
        else getOutputString greedySample
    let mutable sampledTrees = [(greedySampleString, (greedySample, prob))]
    let mutable sampleCount = 0
    while List.length sampledTrees < numPredictions do
        sampleCount <- sampleCount + 1
        varIdx := 1
        let (sampledTree, prob) = predictTree environments true maxNumProdAllowed
        let sampledTreeString = getOutputString sampledTree
        if (sampleCount > numPredictions + 5) || List.forall (fst >> (<>) sampledTreeString) sampledTrees then //Is it new?
            sampledTrees <- (sampledTreeString, (sampledTree, prob)) :: sampledTrees

    (greedySampleString, sampledTrees)

/// Calculate the probability of a syntax tree given a predictor and heap graph features.
let CalculateSyntaxTreeProb
        (mlwrapper : ModelWrapper)
        (syntaxTree : SyntaxTree)
        (environments: Environment list)
        (evalInfo : PredictionEvaluationInformation)
        debug =
    if debug then printfn "Computing probability of syntax tree %s" (syntaxTree.ToStringDetailed ())
    let logProb = ref 0.
    let stackVariables = (environments |> List.head |> snd).Keys |> Seq.map (fun var -> var.Name)

    let jointHeapGraphFeatures = Features.ExtractHeapGraphFeatures environments

    let rec visitNode (currentNode : Node) (environments : Environment list) isOutermostSymheap =
        if not currentNode.IsTerminal then
            let contextFeatures = SparseFeatures()
            let mutable newEnvironments = environments
            match currentNode.NodeType with
            | Expression ->
                //Get features for all known var bindings & predict, then sum up the intermediate results, and choose by maximum
                let expressionsWithFeatures = Features.ComputeExpressionFeatures stackVariables environments syntaxTree currentNode ""
                let exprPosId = syntaxTree.GetExprNodePosDescriptor currentNode
                let (expressions, probabilities) = mlwrapper.PredictExprProductions exprPosId expressionsWithFeatures
                let groundTruthExpression = syntaxTree.GetNameFromExpressionNode currentNode
                let exprWithProbabilities = Array.zip expressions probabilities
                let chosenExpr = fst (Array.maxBy snd exprWithProbabilities)
                evalInfo.NoteNodeTypePredictionResult Expression (chosenExpr = groundTruthExpression)
                if debug && exprWithProbabilities.Length > 1 then
                    printfn " Probabilities of expressions for %i:%s (ground truth: %s):" currentNode.Id (currentNode.NodeType.ToString()) groundTruthExpression
                    for (expr, prob) in exprWithProbabilities do
                        let (_, _, features) = List.find (fun (_, e, _) -> e = expr) expressionsWithFeatures
                        let mark = if groundTruthExpression = expr then "*" else " "
                        printfn " %s{p=%.4f} %s (%s)" mark prob expr (features.ToString())

                let groundTruthProbability =
                    match Array.tryFind (fun (e, _) -> e = groundTruthExpression) exprWithProbabilities with
                    | Some (_, s) -> s
                    | _ -> 0.
                logProb := !logProb + log(groundTruthProbability)
            | ExistentialBinding -> () //These are generated by the symheap special case, and do not need to be considered again here
            | Symheap ->
                let boundExistentialVars = ref []
                let mutable tNode = syntaxTree.GetChildren currentNode |> Seq.tryFind (fun (n : SyntaxTree.Node) -> n.NodeType = ExistentialBinding)
                while tNode.IsSome do
                    boundExistentialVars :=
                          (syntaxTree.GetChildren tNode.Value
                        |> Seq.find (fun (n : SyntaxTree.Node) -> n.NodeType.IsVar)
                        |> syntaxTree.GetNameFromExpressionNode |> SepLogic.VarAddr) :: !boundExistentialVars
                    tNode <- syntaxTree.GetChildren tNode.Value |> Seq.tryFind (fun (n : SyntaxTree.Node) -> n.NodeType = ExistentialBinding)
                let subHeapEnvironments = ComputeSubheapStartsAndNewEnvironments syntaxTree currentNode environments

                //We only need to consider the case when new environments exist (otherwise we are totally lost anyway):
                if subHeapEnvironments.Length <= 0 then
                    newEnvironments <- []
                else
                    let subHeapStartsExistentialsAndEnvironments =
                        if isOutermostSymheap then
                            let addGroundTruthExistentials ((subheapStarts, ((heapGraph, _) as oldEnv), newEnv) : (bigint seq * Environment * Environment)) =
                                let existentials = if heapGraph.HasExistentialInformation then Some heapGraph.SubheapStartsToExistentials.[bigint.MinusOne] else None
                                (oldEnv, newEnv, subheapStarts, existentials)
                            List.map addGroundTruthExistentials subHeapEnvironments
                        else
                            let addGroundTruthExistentials ((subheapStarts, ((heapGraph, _) as oldEnv), newEnv) : (bigint seq * Environment * Environment)) =
                                assert (1 = Seq.length subheapStarts)
                                let subheapStartAddr = Seq.head subheapStarts
                                (oldEnv, newEnv, subheapStarts, Some heapGraph.SubheapStartsToExistentials.[subheapStartAddr])
                            List.map addGroundTruthExistentials subHeapEnvironments
                    let (logProbOfChoices, existentialsWithEnvironments) =
                        PredictExistentiallyQuantified mlwrapper subHeapStartsExistentialsAndEnvironments false null (ref System.Int32.MaxValue) (Some evalInfo) (Some (List.length !boundExistentialVars)) debug
                    logProb := !logProb + logProbOfChoices

                    //Add the existentials to the variable bindings:
                    newEnvironments <-
                        existentialsWithEnvironments
                        |> List.map
                            (fun ((heapGraph, varEnv), existentials) ->
                                (heapGraph, Map.union (Map.ofSeq (Seq.zip !boundExistentialVars (State.Value.addrSeqToValSeq existentials))) varEnv))
                ()
            | Variable -> () //Nothing to do here, it's chosen automatically.
            | PureFormula -> () //Nothing to do here, it's computed deterministically.
            | _ ->
                let features = GetFeaturesForProductionStep contextFeatures jointHeapGraphFeatures environments stackVariables syntaxTree currentNode
                let productionProbabilities = uncurry Array.zip <| mlwrapper.PredictNonterminalProductions features currentNode
                let groundTruthChildren =
                    STProduction(System.Collections.Generic.List(syntaxTree.GetChildren currentNode |> Seq.map (fun n -> n.NodeType)))
                let productionProb =
                    productionProbabilities
                    |> Array.find (fst >> groundTruthChildren.Equals)
                    |> snd
                if debug && productionProbabilities.Length > 1 then
                    let groundTruthString = groundTruthChildren.ToString()
                    printfn " Probabilities of productions for %i:%s (ground truth: %s):" currentNode.Id (currentNode.NodeType.ToString()) groundTruthString
                    printfn "  Features: %s" (features |> Seq.map (fun (feature, value) -> sprintf "%s:%.2f" feature value) |> String.concat " ")
                    for (prod, prob) in productionProbabilities do
                        let prodString = prod.ToString()
                        let mark = if groundTruthString = prodString then "*" else " "
                        printfn " %s{p=%.4f} %s" mark prob prodString
                evalInfo.NoteNodeTypePredictionResult
                    currentNode.NodeType
                    (groundTruthChildren.Equals (fst (Array.maxBy snd productionProbabilities)))
                logProb := !logProb + log(productionProb)

            if currentNode.NodeType <> PureFormula then
                for childNode in syntaxTree.GetChildren currentNode do
                    visitNode childNode newEnvironments false

    try
        visitNode syntaxTree.root environments true
    with
    | ex ->
        printfn "Error CalculateSyntaxTreeProb: %s. Returning prob 0. Syntax Tree: %s" (ex.Message) (syntaxTree.ToCanonicalString())
        logProb := 0.
    exp !logProb
