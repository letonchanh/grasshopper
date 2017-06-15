open System
open System.IO
open Microsoft.FSharp.Collections
open FSharp.Collections.ParallelSeq
open Chiron

open IOUtils
open State
open Utils
open SyntaxTree
open MLWrapper
open DataSet

///Generate a set of SL formulas using the known inductive predicates, parametrized in the number of variables / nesting
let private CreateInitialFormulas (dataConfiguration : DataConfiguration) =
    let varList = [ for i in 0 .. (dataConfiguration.NumberOfVariables - 1) do yield (SepLogic.VarAddr (sprintf "arg%i" i)) ]
    let formulas =
        SepLogic.GuessInitialSymHeaps varList dataConfiguration.DataStructureNestDepth true (ref 0)
        |> Seq.filter (fun (f : SepLogic.SymHeap) -> f.Predicates.Count + f.PointsTos.Count <> 0)
        |> List.ofSeq
    let formulaNumber = List.length formulas

    // Clean up formula directory first
    IOUtils.CleanDirectory dataConfiguration.FormulaDirectory

    printfn "Dumping %i initial formulas" formulaNumber
    let mutable fCounter = 0
    for f in formulas do
        let outFileInfo = dataConfiguration.FormulaFile fCounter
        IOUtils.SerializeData outFileInfo (f, dataConfiguration, fCounter)
        fCounter <- fCounter + 1
        //printfn "  %s" (f.ToString())
        //printfn "  %s" ((SyntaxTree.fromSepLogicformula f).ToString())
        printf "."
    printfn " Done!"

/// Checks if a formula only has nested substructures using one lambda variable
let private isGNNAppropriateFormula (formula : SepLogic.SymHeap) =
    //Outer: Always fine. Inner: Only fine if only the second (for trees) or third (for lists) lambda-bound var is used
    let rec loop (pred : SepLogic.Predicate) knownVariables =
        //Step 1: Check variables, Step 2:
        let thisRes = Seq.fold (fun res (e : SepLogic.Expr) -> res && Set.containsAll e.Variables knownVariables) true pred.Arguments
        let subRes =
            match pred.TypeParameter with
            | None -> true
            | Some subHeap ->
                let newKnowns =
                    match pred.PredicateName with
                    | SepLogic.List -> Set.add subHeap.FreeVars.[2] (Set.addAll subHeap.ExVars knownVariables)
                    | SepLogic.Tree -> Set.add subHeap.FreeVars.[1] (Set.addAll subHeap.ExVars knownVariables)
                Seq.fold (fun res pred -> res && loop pred newKnowns) true subHeap.Predicates
        thisRes && subRes
    let knownVariables = formula.AllVars |> Set.ofSeq
    Seq.fold (fun res pred -> res && loop pred knownVariables) true formula.Predicates

let private CreateStatesForFormula (dataConfiguration : DataConfiguration) (generateGNNData : bool) formulaFile =
    let statesToSkip = 0;
    let (formula, _, formulaIndex) : (SepLogic.SymHeap * DataConfiguration * int) = IOUtils.DeserializeData formulaFile

    let isAppropriateFormula =
        if generateGNNData then
            isGNNAppropriateFormula
        else
            fun _ -> true

    if isAppropriateFormula formula then
        use modelGenerator = SepLogic.SepLogicModelEnumerator.create formula formula.FreeVars formula.ExVars
        let stateList = System.Collections.Generic.List(dataConfiguration.NumberOfHeapsPerFormula)
        let mutable stateCounter = 0
        printfn " %i: %s: %s" System.Threading.Thread.CurrentThread.ManagedThreadId formulaFile (formula.ToString())
        while modelGenerator.MoveNext() && stateCounter - statesToSkip < dataConfiguration.NumberOfHeapsPerFormula do
            if stateCounter >= statesToSkip then
                stateList.Add (stateCounter, modelGenerator.Current)
            stateCounter <- stateCounter + 1
        let outFileInfo = dataConfiguration.StateSetFile formulaIndex
        IOUtils.SerializeData outFileInfo (formula, formulaIndex, stateList)
        1
    else
        0

let private CreateStates (dataConfiguration : DataConfiguration) (generateGNNData : bool) (formulaFiles : string []) (formulasToTake : int) =
    printfn "Creating states for %i formulas:" formulasToTake

    // Clean up state directory first
    IOUtils.CleanDirectory dataConfiguration.StateSetDirectory

    let mutable curBeginIndex = 0
    let mutable takenSoFar = 0
    while takenSoFar < formulasToTake && curBeginIndex < formulaFiles.Length do
        let sliceLength = min (formulasToTake - takenSoFar) (formulaFiles.Length - curBeginIndex)
        let approxFormulaSlice = System.ArraySegment(formulaFiles, curBeginIndex, sliceLength)
        let takenFormulas =
            approxFormulaSlice
            |> PSeq.map (CreateStatesForFormula dataConfiguration generateGNNData)
            |> PSeq.sum
        takenSoFar <- takenSoFar + takenFormulas
        curBeginIndex <- curBeginIndex + sliceLength
    printfn "Done."

let private RunProgram programFile dataDirName rng =
    let parseProgram filename =
        use inchan = File.OpenText filename
        let lexbuf = Microsoft.FSharp.Text.Lexing.LexBuffer<char>.FromTextReader inchan
        let res = HeapImpParse.program HeapImpFlex.token lexbuf
        res

    let dumpInfo = {
        IOUtils.DumpInfo.Directory = DirectoryInfo(Path.Combine(dataDirName, sprintf "%s_state-dumps" programFile));
        IOUtils.DumpInfo.DumpIdToCounter = Map.empty;
        IOUtils.DumpInfo.DumpedFiles = [];
    }

    printfn "Parsing %s" programFile
    let program = parseProgram programFile
    printf "Starting evaluation ..."

    let _ = ProgramEval.eval program dumpInfo rng [3]
    printfn " Done. Dumped files: "
    for f in dumpInfo.DumpedFiles do
        printfn "  %s" f

let private CreateDatasetForState (dataConfiguration : DataConfiguration) instanceToDataSetType groupSize rng sampleRatio generateGNNData gnnDataZip stateSetFile =
    try
        // Get data, turn formula into canonical form:
        let (formula, formulaId, stateSet) : (SepLogic.SymHeap * int * Collections.Generic.List<int * (State.State * (Map<SepLogic.TypedVar, State.Addr> * ListDictionary<State.Addr, State.Addr>))>) =
            IOUtils.DeserializeData (stateSetFile)
        let instanceDataSetType = instanceToDataSetType formulaId
        let (syntaxTree, variableNameNormaliser) = SyntaxTree.fromSepLogicFormula formula

        let dataSetSymbol =
            match instanceDataSetType with
            | IOUtils.DataSetType.Training   -> "*"
            | IOUtils.DataSetType.Validation -> "+"
            | IOUtils.DataSetType.Test       -> "?"
        printfn "%s(%i): %s" dataSetSymbol System.Threading.Thread.CurrentThread.ManagedThreadId stateSetFile

        // Store away canonical formula representation:
        let formulaOutFile = new FileInfo(dataConfiguration.FormulaTextFilePath (instanceDataSetType, formulaId))
        formulaOutFile.Directory.Create()
        use formulaOutStream = formulaOutFile.CreateText()
        formulaOutStream.WriteLine(formula.ToString())

        // Prepare some information that we'll need:
        let productionStore = ProductionStore()
        let mutable addrGroupCounter = 0
        let mutable exprGroupCounter = 0
        use outputStreamCache = new OutputStreamCache()

        let stateSet = Array.ofSeq stateSet
        KnuthShuffle rng stateSet

        // Go through the instances we have for this state:
        let mutable stateGroupIndex = 0
        let seenExpressions = System.Collections.Generic.HashSet()
        let statesToTake = int (sampleRatio * float (stateSet.Length - 1))
        while stateGroupIndex + groupSize <= statesToTake do
            let stateGroup = Array.sub stateSet stateGroupIndex groupSize
            ///Graph Export for GNN code:
            if generateGNNData then
                for (graphId, (state, (exVarToVal, subheapStartToExVarsVals))) in stateGroup do
                    GraphExport.ExtractAnnotationSteps gnnDataZip instanceDataSetType formulaId graphId formula state exVarToVal subheapStartToExVarsVals

            stateGroupIndex <- stateGroupIndex + groupSize

            let envsWithExVarInformation =
                [ for (_, (state, (exVarToAddr, startOfSubheapToExVars))) in stateGroup do
                    let exVarNameToAddrVal = exVarToAddr |> Seq.map (fun kv -> (SepLogic.VarAddr variableNameNormaliser.[kv.Key.Name], ValAddr kv.Value)) |> Map.ofSeq
                    yield ((HeapGraph(AnnotatedGraph(state.asGraph ()), Some startOfSubheapToExVars), Features.varEnvFromVarStack state.varStack), exVarNameToAddrVal)
                ]
            let groupId = String.concat "," (Array.map (fst >> string) stateGroup)

            ///// Get training data for all nonterminal productions.
            ///// These are composed of overall heap features and local heap and syntax tree features.
            let (nodeTypeToFeatureAndProductionPairs, addressGroupFeatures, allExprFeatures) =
                Features.ComputeProductionFeaturesFromSyntaxTree envsWithExVarInformation syntaxTree

            ///// Part 1: "Generic" productions, which can be handled through multiclass support in TLC:
            for (nodeType, productionAndFeaturePairs) in nodeTypeToFeatureAndProductionPairs do
                let dataWriter = outputStreamCache.GetOutputStream (dataConfiguration.PartialDataSetFile (instanceDataSetType, formulaId, (nodeType.ToString())))
                for (production, features) in productionAndFeaturePairs do
                    let childrenIdx = productionStore.NoteProduction nodeType production
                    dataWriter.Write("_{0:D},{1:D}\t{2:D}\t", formulaId, groupId, childrenIdx)
                    features.ToNamedFeatureStringToWriter dataWriter
                    dataWriter.WriteLine()

            ///// Part 2: Get training data for "special" addresses, i.e., those which we want to name using exist. variables
            ///// These are made up of local heap features
            for addressGroup in addressGroupFeatures do
                let dataWriter = outputStreamCache.GetOutputStream (dataConfiguration.PartialDataSetFile (instanceDataSetType, formulaId, "addr"))
                for (isEx, addr, features) in addressGroup do
                    dataWriter.Write("{0}-{1}\t{2}\t{3},{4},{5}\t", formulaId, addrGroupCounter, (if isEx then 1 else 0), formulaId, groupId, addr)
                    features.ToNamedFeatureStringToWriter dataWriter
                    dataWriter.WriteLine()
                addrGroupCounter <- addrGroupCounter + 1

            ///// Part 3: Get training data for "expr" productions that determine used variables.
            ///// These are composed of local heap features and local syntax features.
            for (exprPos, exprFeatureGroups) in allExprFeatures do
                seenExpressions.Add exprPos |> ignore
                for exprGroup in exprFeatureGroups do
                    let dataWriter = outputStreamCache.GetOutputStream (dataConfiguration.PartialDataSetFile (instanceDataSetType, formulaId, exprPos))
                    let mutable foundExpr = false
                    for (isChosen, expr, features) in exprGroup do
                        dataWriter.Write(
                            "{0}-{1}\t{2}\t{3},{4},{5}\t",
                            formulaId, exprGroupCounter,
                            (if isChosen then 1 else 0),
                            formulaId, groupId, expr)
                        features.ToNamedFeatureStringToWriter dataWriter
                        foundExpr <- foundExpr || isChosen
                        dataWriter.WriteLine()
                    if not foundExpr then System.Diagnostics.Debugger.Launch() |> ignore
                    exprGroupCounter <- exprGroupCounter + 1

            ///// Part 4: Also store the state as a text file:
            for (stateId, (state, (exVarToAddr, startOfSubheapToExVars))) in stateGroup do
                State.stackAndHeapGraphToFile state.varStack (state.asGraph()) (dataConfiguration.StateTextFilePath (instanceDataSetType, formulaId, stateId))
                let exVarNameToAddr = exVarToAddr |> Seq.map (fun kv -> kv.Key.Name, kv.Value) |> Map.ofSeq
                IOUtils.SaveExistentialMaps (dataConfiguration.ExistentialMapTextFilePath (instanceDataSetType, formulaId, stateId)) exVarNameToAddr startOfSubheapToExVars

        ///// Part 5: Store away all generated data:
        IOUtils.SerializeData (dataConfiguration.PartialProductionStoreFile (instanceDataSetType, formulaId)) productionStore

        for nodeType in productionStore.GetNodeTypes() do
            let nonterminalFile = System.IO.FileInfo(dataConfiguration.PartialDataSetUsedNonterminalFile (nodeType.ToString()))
            while not nonterminalFile.Exists do
                try
                    IOUtils.SerializeData nonterminalFile.FullName nodeType
                with
                | _ -> eprintfn "Could not write nonterminal information file -- retrying."
                nonterminalFile.Refresh()

        for exprPos in seenExpressions do
            let exprFile = System.IO.FileInfo(Path.Combine (dataConfiguration.PartialDataSetUsedExprDir, exprPos))
            while not exprFile.Exists do
            try
                SerializeData exprFile.FullName exprPos
            with
            | _ -> eprintfn "Could not write expr information file -- retrying."
            exprFile.Refresh()
            ()

    with
    | ex -> eprintfn "Thread %i on %s failed:\n%s" System.Threading.Thread.CurrentThread.ManagedThreadId stateSetFile (ex.ToString())

/// <summary>
/// Create training, validation and test datasets, in partial files. For internal use, we generate CSV
/// files for each occurring nonterminal, and for external use, pairs of files with textual
/// representations of states and corresponding formulas.
/// </summary>
let private CreateDataset (dataConfiguration : DataConfiguration) validationDataRatio testDataRatio groupSize rng (stateSetFiles : string []) sampleRatio generateGNNData =
    // Choose which formulas / states go where, set up output infrastructure:
    let (validationStateSetFiles, testStateSetFiles) =
        let shuffledStateSetFiles = stateSetFiles.Clone() :?> string[]
        KnuthShuffle rng shuffledStateSetFiles |> ignore
        let validationFormulaCount = int <| (float stateSetFiles.Length) * validationDataRatio
        let testFormulaCount = int <| (float stateSetFiles.Length) * testDataRatio
        (Collections.Generic.HashSet(shuffledStateSetFiles.[0 .. validationFormulaCount - 1]),
         Collections.Generic.HashSet(shuffledStateSetFiles.[validationFormulaCount .. validationFormulaCount + testFormulaCount - 1]))

    let getInstanceDataSetType formulaId =
        let stateSetFile = dataConfiguration.StateSetFile formulaId
        if validationStateSetFiles.Contains stateSetFile then IOUtils.DataSetType.Validation
        else if testStateSetFiles.Contains stateSetFile  then IOUtils.DataSetType.Test
        else                                                  IOUtils.DataSetType.Training

    use gnnDataZip =
        new System.IO.Compression.ZipArchive(
            new System.IO.FileStream(dataConfiguration.GraphPropertyDatasetZip, System.IO.FileMode.Create),
            System.IO.Compression.ZipArchiveMode.Create,
            false) //This last parameter makes sure that stream is properly disposed of when we dispose the zip archive

    // Clean up dataset directory first
    IOUtils.CleanDirectory dataConfiguration.DatasetDir
    IOUtils.CleanDirectory dataConfiguration.MLDataDir

    // Go through the actual data:
    stateSetFiles
    |> PSeq.iter (CreateDatasetForState dataConfiguration getInstanceDataSetType groupSize rng sampleRatio generateGNNData gnnDataZip)

let private CombineInternalCSVFormat (dataConfiguration : DataConfiguration) nonterminal (featureNameToIndex : Features.FeatureToIndexMap) dataSetType =
    let combinedFile = dataConfiguration.DataSetFile (dataSetType, nonterminal)
    use combinedOutStream = new System.IO.StreamWriter(IOUtils.GetOutStream combinedFile)
    let partialDirectory = DirectoryInfo (dataConfiguration.PartialDataSetDir)
    let partialFilePattern = dataConfiguration.PartialDataSetFilePattern (dataSetType, nonterminal)
    let mutable curNumericId = -1
    let mutable curId = ""
    let mutable lineCounter = 0
    for partialFileInfo in partialDirectory.GetFiles partialFilePattern do
        use partialInStream = new System.IO.StreamReader(IOUtils.GetInStream partialFileInfo.FullName)
        while not partialInStream.EndOfStream do
            let line = partialInStream.ReadLine()
            lineCounter <- lineCounter + 1
            // Slightly sorry for the following, but this code is the bottleneck in the combination.
            // line.Split(\t) would be easier, but require going over the string several times
            let mutable firstIdxInThisBuffer = 0
            let mutable separatorIdxInThisBuffer = 0
            let mutable inData = false
            let mutable inLabel = false
            let mutable inId = false
            // Column format: "WorkerId-GroupId\tIsChosenId\tEntryId\t
            for curCharIdx in 0 .. line.Length - 1 do
                let curChar = line.Chars curCharIdx

                if curChar = '\t' then
                    if inData then
                        let featureName = line.Substring (firstIdxInThisBuffer, separatorIdxInThisBuffer - firstIdxInThisBuffer)
                        let colonWithFeatureValue = line.Substring (separatorIdxInThisBuffer, curCharIdx - separatorIdxInThisBuffer)
                        let featureIdx = featureNameToIndex.GetFeatureId featureName
                        combinedOutStream.Write('\t')
                        combinedOutStream.Write(featureIdx)
                        combinedOutStream.Write(colonWithFeatureValue)
                    else
                        let thisId = line.Substring (firstIdxInThisBuffer, curCharIdx - firstIdxInThisBuffer)
                        if inLabel then
                            combinedOutStream.Write("\t{0}", thisId)
                            inData <- true
                        else if inId then
                            combinedOutStream.Write("\t{0}", thisId)
                            inLabel <- true //Mark that we are done with the string ID
                        else //We are in the "numeric" index part, which we need to fix to a number:
                            let thisNumericId =
                                if thisId <> curId then
                                    curNumericId <- curNumericId + 1
                                    curId <- thisId
                                curNumericId
                            combinedOutStream.Write(thisNumericId)
                            inId <- true //Mark that we are done with the numeric ID
                    //Prepare for the next part of the data:
                    firstIdxInThisBuffer <- curCharIdx + 1
                else if inData && curChar = ':' then
                    separatorIdxInThisBuffer <- curCharIdx
            combinedOutStream.WriteLine()
        partialInStream.Close()
        partialFileInfo.Delete()

    printf " (%s)" (dataSetType.ToString())
    lineCounter

let private CombineTLCCSVFormatFiles (dataConfiguration : DataConfiguration) nonterminalNodeType (featureNameToIndex : Features.FeatureToIndexMap) (globalProductionStore : ProductionStore) (productionStoreCache : IOUtils.DataSetType -> int -> ProductionStore) dataSetType =
    let nonterminalName = nonterminalNodeType.ToString()
    let combinedFile = dataConfiguration.DataSetFile (dataSetType, nonterminalName)
    use combinedOutStream = new System.IO.StreamWriter(IOUtils.GetOutStream combinedFile)
    let partialDirectory = DirectoryInfo (dataConfiguration.PartialDataSetDir)
    let partialFilePattern = dataConfiguration.PartialDataSetFilePattern (dataSetType, nonterminalName)
    for partialFileInfo in partialDirectory.GetFiles partialFilePattern do
        let res = DataConfiguration.PartialDataSetFileRegularExpression.Match partialFileInfo.Name
        assert (res.Success)
        let formulaId = System.Int32.Parse res.Groups.[3].Value
        let formulaProductionStore = productionStoreCache dataSetType formulaId
        use partialInStream = new System.IO.StreamReader(IOUtils.GetInStream partialFileInfo.FullName)
        //Fix up numerical IDs of productions here, translate feature names into feature IDs:
        while not partialInStream.EndOfStream do
            let line = partialInStream.ReadLine()
            // Slightly sorry for the following, but this code is the bottleneck in the combination.
            // line.Split(\t) would be easier, but require going over the string several times
            let mutable firstIdxInThisBuffer = 0
            let mutable separatorIdxInThisBuffer = 0
            let mutable inData = false
            let mutable inProductionId = false
            for curCharIdx in 0 .. line.Length - 1 do
                let curChar = line.Chars curCharIdx
                if curChar = '\t' then
                    if inData then
                        let featureName = line.Substring (firstIdxInThisBuffer, separatorIdxInThisBuffer - firstIdxInThisBuffer)
                        let colonWithFeatureValue = line.Substring (separatorIdxInThisBuffer, curCharIdx - separatorIdxInThisBuffer)
                        let featureIdx = featureNameToIndex.GetFeatureId featureName
                        combinedOutStream.Write('\t')
                        combinedOutStream.Write(featureIdx)
                        combinedOutStream.Write(colonWithFeatureValue)
                    else
                        let thisId = line.Substring (firstIdxInThisBuffer, curCharIdx - firstIdxInThisBuffer)
                        if inProductionId then //We are in the production ID, which we need to rewrite to the global production IDs
                            let productionId = int thisId
                            let production = formulaProductionStore.GetProduction nonterminalNodeType productionId
                            let globalProductionId = globalProductionStore.NoteProduction nonterminalNodeType production
                            combinedOutStream.Write("\t{0}", globalProductionId)
                            inData <- true //Mark that we are done with the string ID
                        else //We are in the line id part, which we just need to copy:
                            combinedOutStream.Write(thisId)
                            inProductionId <- true //Mark that we are done with the line ID
                    //Prepare for the next part of the data:
                    firstIdxInThisBuffer <- curCharIdx + 1
                else if inData && curChar = ':' then
                    separatorIdxInThisBuffer <- curCharIdx
            combinedOutStream.WriteLine()
        partialInStream.Close()
        partialFileInfo.Delete()
    printf " (%s)" (dataSetType.ToString())

let private CombinePartialDatasetData (dataConfiguration : DataConfiguration) =
    let mutable variableNonterms = []

    // Combine the training data for variable predictors: expr and addr
    let exprFiles =
        System.IO.Directory.GetFiles dataConfiguration.PartialDataSetUsedExprDir
        |> Seq.map Path.GetFileName
    for nonterminal in Seq.append ["addr"] exprFiles do
        let featureNameToIndex = Features.FeatureToIndexMap()
        printf "Combining data for %s" nonterminal
        [ IOUtils.Training ; IOUtils.Validation ; IOUtils.Test ]
        |> PSeq.map (fun dsT -> (dsT, CombineInternalCSVFormat dataConfiguration nonterminal featureNameToIndex dsT))
        |> List.ofSeq //this is so that the computation blocks here until all datasets have been processed...
        |> ignore
        printfn ""

        variableNonterms <- (nonterminal, featureNameToIndex) :: variableNonterms
        printfn " Saving %i mappings from observed %s feature names to indices." featureNameToIndex.Count nonterminal
        IOUtils.SerializeData (dataConfiguration.NonterminalFeatureToFeatureIndexMapFile nonterminal) featureNameToIndex

    // Combine all the different production stores lazily
    let productionStoreCacheDict = System.Collections.Concurrent.ConcurrentDictionary<IOUtils.DataSetType * int, ProductionStore>()
    let productionStoreCache dataSetType formulaId =
        productionStoreCacheDict.GetOrAdd
            ((dataSetType, formulaId),
             System.Func<IOUtils.DataSetType * int, ProductionStore>
                (fun _ ->
                    let prodStore : SyntaxTree.ProductionStore =
                        IOUtils.DeserializeData (dataConfiguration.PartialProductionStoreFile (dataSetType, formulaId))
                    prodStore))

    // Combine all the "generic" nonterminal training data
    let partialNonterminalInfoDirPath = dataConfiguration.PartialDataSetUsedNonterminalDir
    let partialNonterminalInfoDir = System.IO.DirectoryInfo partialNonterminalInfoDirPath
    let featuresToIndices = Features.FeatureToIndexMap()
    let productionStore = ProductionStore()
    for f in partialNonterminalInfoDir.GetFiles() do
        let nodeType : NodeType = IOUtils.DeserializeData f.FullName
        printf "Combining data for %s" (nodeType.ToString())
        PSeq.iter (CombineTLCCSVFormatFiles dataConfiguration nodeType featuresToIndices productionStore productionStoreCache) [ IOUtils.Training ; IOUtils.Validation ; IOUtils.Test ]
        printfn ""

    IOUtils.SerializeData (dataConfiguration.ProductionStoreFile) productionStore
    IOUtils.SerializeData (dataConfiguration.FeatureToFeatureIndexMapFile) featuresToIndices
    // Write some meta information for the ML trainer
    let metadata =
        Object <| Map.ofList [
            ("generic_num_features", featuresToIndices.Count |> decimal |> Number);
            ("nonterm_to_num_labels",
                [
                for nodeType in productionStore.GetNonTrivialNodeTypes() ->
                    (nodeType.ToString(),
                        (productionStore.GetIdToProduction nodeType).Count
                        |> decimal |> Number)
                ]
                |> Map.ofList |> Object
            );
            ("generic_feature_map", featuresToIndices.ToJson());
            ("ident_to_num_features",
                variableNonterms
                |> List.map (fun (n, fMap) -> (n, fMap.Count |> decimal |> Number))
                |> Map.ofList
                |> Object);
            ("ident_to_feature_map",
                Object <| Map.ofList (
                    variableNonterms
                    |> List.map (fun (n, fMap) -> (n, fMap.ToJson()))
                )
            );
        ]
    use metaStream = new System.IO.StreamWriter(GetOutStream (dataConfiguration.MetaInfoFile))
    metaStream.WriteLine(Json.format metadata)

    printfn " Saving %i mappings from observed feature names to indices." featuresToIndices.Count

let private TrainModel (dataConfiguration : DataConfiguration) =
    printfn "Training model from dataset from folder: %s" dataConfiguration.MLDataDir

    // train and save TLC model
    SoftmaxModelWrapper.TrainAndSaveModel dataConfiguration

let private PredictHeapDescription (dataConfiguration : DataConfiguration) modelName temperature numberOfPredictions (envs : Features.Environment list) insertBtwns debugMode =
    use mlmodelwrapper = new SoftmaxModelWrapper(dataConfiguration, modelName, temperature)
    let results =
        Predictor.PredictSyntaxTree mlmodelwrapper envs numberOfPredictions false insertBtwns debugMode
        |> snd
        |> List.sortBy (fun (_, (_, p)) -> -p) //Sort by descending probability
    results
    |> List.iter (fun (predictedSyntaxTreeStr, (_, prob)) -> printfn "Prediction {p=%.4f}: %s" prob predictedSyntaxTreeStr)

    if debugMode && (fst (List.head envs)).HasExistentialInformation then
        let mostLikelyFormula = fst (snd (List.head results))
        let evalInfo = Predictor.PredictionEvaluationInformation(numberOfPredictions)
        envs
        |> List.iteri
            (fun i env ->
                let groundtruthProb = Predictor.CalculateSyntaxTreeProb mlmodelwrapper mostLikelyFormula [env] evalInfo false
                printfn "Prob for %i: {p=%.4f}" i groundtruthProb)

let private PredictHeapDescriptionFromSerializedState (dataConfiguration : DataConfiguration) modelName modelConfiguration numberOfPredictions stateFiles debugMode =
    let envs =
        stateFiles
        |> List.map
            (fun f ->
                let state : State = IOUtils.DeserializeData f
                (HeapGraph(AnnotatedGraph(state.asGraph())), Features.varEnvFromVarStack state.varStack))
    PredictHeapDescription dataConfiguration modelName modelConfiguration numberOfPredictions envs false debugMode

let private PredictHeapDescriptionFromGHPState (dataConfiguration : DataConfiguration) modelName temperature numberOfPredictions ghpStateFiles insertBtwns debugMode =
    //We are going to parse external states, so kill our default data field IDs:
    Utils.ClearDataFields()
    let envs =
        ghpStateFiles
        |> List.map
            (fun f ->
                let (varStack, heapGraph) = GHPState.parse f
                (HeapGraph(AnnotatedGraph(heapGraph)), Features.varEnvFromVarStack varStack))
        |> Features.restrictEnvsToCommonVars
    // First predict formulas for all states
    use mlmodelwrapper = new SoftmaxModelWrapper(dataConfiguration, modelName, temperature)
    let results =
        Predictor.PredictSyntaxTree mlmodelwrapper envs numberOfPredictions false insertBtwns debugMode
        |> snd
        |> List.sortBy (fun (_, (_, p)) -> -p) //Sort by descending probability
    results
    |> List.iter (fun (predictedSyntaxTreeStr, (_, prob)) -> printfn "Prediction {p=%.4f}: %s" prob predictedSyntaxTreeStr)
    // Then, predict some disjunctive ones
    Clustering.featureCluster envs mlmodelwrapper insertBtwns debugMode |> ignore

let private PredictDisjunctiveHeapDescription (dataConfiguration : DataConfiguration) modelName temperature ghpStateFiles insertBtwns debugMode =
    //We are going to parse external states, so kill our default data field IDs:
    Utils.ClearDataFields()
    let envs =
        ghpStateFiles
        |> List.map
            (fun f ->
                let (varStack, heapGraph) = GHPState.parse f
                (HeapGraph(AnnotatedGraph(heapGraph)), Features.varEnvFromVarStack varStack))
        |> Features.restrictEnvsToCommonVars
    use mlmodelwrapper = new SoftmaxModelWrapper(dataConfiguration, modelName, temperature)
    let clusters = Clustering.featureCluster envs mlmodelwrapper insertBtwns debugMode
    if List.length clusters <> 0 then
        let clusters =
            clusters
           |> List.map (fun x -> x.ToString())
           |> List.sort
           |> String.concat " || "
        printfn "Prediction {p=0.0000}: %s" clusters

let private queryMode (dataConfiguration : DataConfiguration) modelName temperature numberOfPredictions insertBtwns debugMode =
    use mlmodelwrapper = new SoftmaxModelWrapper(dataConfiguration, modelName, temperature)
    while Console.ReadLine() = "Query" do
        let query = (Console.ReadLine ()).Split [|':'|]
        let queryType, fileNames = query.[0].Trim(), query.[1].Trim()
        //We are going to parse external states, so kill our default data field IDs:
        Utils.ClearDataFields()
        let envs =
            fileNames.Split [|' '|]
            |> Array.toList
            |> List.map
                (fun f ->
                    let (varStack, heapGraph) = GHPState.parse f
                    (HeapGraph(AnnotatedGraph(heapGraph)), Features.varEnvFromVarStack varStack))
            |> Features.restrictEnvsToCommonVars
        match queryType with
        | "single" ->
            let results =
                Predictor.PredictSyntaxTree mlmodelwrapper envs numberOfPredictions false insertBtwns debugMode
                |> snd
                |> List.sortBy (fun (_, (_, p)) -> -p) //Sort by descending probability
            results
            |> List.iter (fun (predictedSyntaxTreeStr, (_, prob)) -> printfn "Prediction {p=%.4f}: %s" prob predictedSyntaxTreeStr)
        | "disjunction" ->
            Clustering.featureCluster envs mlmodelwrapper insertBtwns debugMode |> ignore
        | _ ->
            failwithf "Expected query type to be single/disjunction, got %s." queryType
        printfn "Done"
        Console.Out.Flush()

let private PredictHeapDescriptionFromDatasetState (dataConfiguration : DataConfiguration) modelName temperature groupSize numberOfPredictions (idString : string) rng debugMode =
    use mlmodelwrapper = new SoftmaxModelWrapper(dataConfiguration, modelName, temperature)
    let runPredictor formula (environments : Features.Environment list) =
        environments |> List.iteri
            (fun i (heapGraph, varEnv) ->
                 let outFileInfo = FileInfo(sprintf "debugHeap_%i.dot" i)
                 use outStream = outFileInfo.CreateText();
                 let varEnvRestricted = Map.fold (fun newMap (var : SepLogic.TypedVar) value -> match value with | ValAddr addr -> Map.add var.Name addr newMap | _ -> newMap) Map.empty varEnv
                 heapGraph.Graph.BackingGraph.toDot (varEnvRestricted) outStream
                 outStream.Close())

        let heapGraphFeatures = Features.ExtractHeapGraphFeatures environments
        let (groundTruthSyntaxTree, _) = SyntaxTree.SyntaxTree.fromSepLogicFormula formula

        (*
        let stateSetFile = IOUtils.getStateSetFile dataConfiguration formulaId
        let (_, _, stateSet) : (SepLogic.SymHeap * int * Collections.Generic.List<int * (State.State * (Map<SepLogic.VarName, bigint> * ListDictionary<bigint, bigint>))>) =
            IOUtils.DeserializeData stateSetFile
        let (_, (_, (exVarToAddr, startOfSubheapToExVars))) = Seq.find (fst >> (=) heapId) stateSet
        Features.computeProductionFeaturesFromSyntaxTree heapGraph varStack exVarToAddr startOfSubheapToExVars groundtruthSyntaxTree heapGraphFeatures |> ignore
        *)

        if debugMode then
            printfn "Heap features:\n%s\n" (heapGraphFeatures |> Seq.map (fun (feature, value) -> sprintf "%s: %.2f" feature value) |> String.concat "\n")

        let (_, predictionResults) =
            Predictor.PredictSyntaxTree mlmodelwrapper environments numberOfPredictions true false debugMode
        let sortedResults = predictionResults |> Seq.sortBy (fun (_, (_, p)) -> -p)
        let evalInfo = Predictor.PredictionEvaluationInformation(numberOfPredictions)
        if debugMode then
            printfn "%s" (formula.ToString ())
        environments |> List.iteri
            (fun i env ->
                let groundtruthProb = Predictor.CalculateSyntaxTreeProb mlmodelwrapper groundTruthSyntaxTree [env] evalInfo debugMode
                printfn "Ground truth for %i {p=%.4f}:  %s" i groundtruthProb (groundTruthSyntaxTree.ToCanonicalString ()))
        for (predictedSyntaxTreeStr, (_, predictedProb)) in sortedResults do
            printfn "Predicted          {p=%.4f}:  %s" predictedProb predictedSyntaxTreeStr

    let formulaAndStateRE = System.Text.RegularExpressions.Regex(@"^\s*\(\s*(\d+),\s*([0-9;]+)\s*\)\s*$")
    let res = formulaAndStateRE.Match idString
    if not(res.Success) then
        let formulaRE = System.Text.RegularExpressions.Regex(@"^\s*\(\s*(\d+)\s*\)\s*$")
        let res = formulaRE.Match idString
        if not(res.Success) then
            failwithf "Could not parse ID '%s' (should be in format '(formulaId, heapId(;heapId)*)' or '(formulaId)')!" idString
        else
            let formulaId = System.Int32.Parse res.Groups.[1].Value
            let dataset = new DataSet.DataSet(dataConfiguration.DatasetPartDir IOUtils.DataSetType.Test, groupSize, rng, Some formulaId, None)
            for dataSetElement in dataset do
                let formula = dataSetElement.Formula
                let environments = dataSetElement.StatesWithSubheapToExVars |> List.map snd
                runPredictor formula environments
    else
        let (formulaId, heapIds) = (System.Int32.Parse res.Groups.[1].Value, res.Groups.[2].Value)
        let formula = DataSet.ReadFormulaFromFile (FileInfo(dataConfiguration.FormulaTextFilePath (DataSetType.Test, formulaId)))
        let environments =
            [
                for heapId in heapIds.Split ';' do
                    yield DataSet.ReadStateInfoFromFile (FileInfo(dataConfiguration.StateTextFilePath (DataSetType.Test, formulaId, heapId)))
            ]
        runPredictor formula environments


// ------------------------------------------------------------------------------------------------------------------------------------------

type RunMode =
    | FormulaCreation
    | StateCreation
    | DatasetCreation
    | DatasetCombination
    | ModelTraining
    | ModelEvaluation
    | SerializedStatePrediction
    | DatasetStatePrediction of string
    | GHPStatePrediction
    | ProgramRunner of string
    | DisjunctivePrediction
    | Query
    | Help

[<EntryPoint>]
let main arguments =
    let runMode = ref Help
    let numVars = ref 3
    let dsDepth = ref 0
    let statesPerFormula = ref 250
    let dataDir = ref "data"
    let tfDir = ref "."
    let groupSize = ref 1
    let numberOfPredictions = ref 1
    let sample = ref 1.
    let debug = ref false
    let generateGNNData = ref false
    let lam1, lam2 = ref 0.0, ref 0.0
    let numClusters = ref 2
    let kmcConf = ref 1
    let insertBtwns = ref false
    let temperature = ref 1.0
    let modelName = ref ""

    let optionSet = Mono.Options.OptionSet()
    optionSet
            //The actual run mode:
            .Add( "help"
                , "Show help."
                , fun _ -> runMode := Help)
            .Add( "create-formulas"
                , "Generate initial formulas for chosen parameters."
                , fun _ -> runMode := FormulaCreation)
            .Add( "create-states"
                , "Generate states from initial formulas (depends on created formulas)."
                , fun _ -> runMode := StateCreation)
            .Add( "create-dataset"
                , "Create synthetic data set (depends on created states), in partial files."
                , fun _ -> runMode := DatasetCreation)
            .Add( "combine-dataset"
                , "Combine partial dataset files."
                , fun _ -> runMode := DatasetCombination)
            .Add( "train-model"
                , "Train chosen ML model (depends on created dataset)."
                , fun _ -> runMode := ModelTraining)
            .Add( "evaluate-model"
                , "Evaluate ML model (depends on trained model)."
                , fun _ -> runMode := ModelEvaluation)
            .Add( "run-program="
                , "Run program, dump state at given points."
                , fun (s: string) -> runMode := ProgramRunner s)
            .Add( "predict-state"
                , "Predict a heap formula for states given in serialized format."
                , fun _ -> runMode := SerializedStatePrediction)
            .Add( "predict-dataset-state="
                , "Predict a heap formula for a state in our test dataset (id given as '(formula, states)')."
                , fun (s : string) -> runMode := DatasetStatePrediction s)
            .Add( "predict-ghp-state"
                , "Predict a heap formula for states given in GHP text format."
                , fun _ -> runMode := GHPStatePrediction)
            .Add( "predict-disjunction"
                , "Predict a disjunctive heap formula for states given in GHP text format."
                , fun _ -> runMode := DisjunctivePrediction)
            .Add( "query"
                , "Enter query mode to do multiple predictions."
                , fun _ -> runMode := Query)

            //Options:
            .Add( "temp="
                , sprintf "temperature with which to sample from the TF model [default: %f]." !temperature
                , fun (f: float) -> temperature := f)
            .Add( "kmc-conf="
                , sprintf "configuration of k-Means clustering [default: %d]." !kmcConf
                , fun (s: int) -> kmcConf := s)
            .Add( "lam1="
                , sprintf "parameter for k-Means [default: %f]." !lam1
                , fun (f: float) -> lam1 := f)
            .Add( "lam2="
                , sprintf "parameter for k-Means [default: %f]." !lam2
                , fun (f: float) -> lam2 := f)
            .Add( "num-clusters="
                , sprintf "number of clusters wanted for k-Means [default: %d]." !numClusters
                , fun (i: int) -> numClusters := i)
            .Add( "variable-number="
                , sprintf "Number of variables to consider [default %i]." !numVars
                , fun (i: int) -> numVars := i)
            .Add( "ds-nest-level="
                , sprintf "Number of nested levels of data structures to consider [default %i]." !dsDepth
                , fun (i: int) -> dsDepth := i)
            .Add( "states-per-formula="
                , sprintf "Number of concrete states per symbolic heap [default %i]." !statesPerFormula
                , fun (i: int) -> statesPerFormula := i)
            .Add( "data-dir="
                , sprintf "Directory for created / read data (will use diff. subdirectories for formulas/states/models [default: %s])." !dataDir
                , fun (s: string) -> dataDir := s)
            .Add( "tf-dir="
                , sprintf "Directory containing the tensorflow predictor [default: %s])." !tfDir
                , fun (s: string) -> tfDir := s)
            .Add( "group-size="
                , sprintf "Number of heapgraphs used for training/prediction [default: %i]." !groupSize
                , fun (i: int) -> groupSize := i)
            .Add( "prediction-number="
                , sprintf "Number of predictions made for each input group [default: %i]." !numberOfPredictions
                , fun (i: int) -> numberOfPredictions := i)
            .Add( "sample-ratio="
                , sprintf "Ratio of formulas/states that should be used. [default: %f]." !sample
                , fun (f : float) -> sample := f)
            .Add( "synth-graph-data"
                , "Also generate GNN-input data (combine with --create-dataset)."
                , fun (_ : unit) -> generateGNNData := true)
            .Add( "insert-btwns"
                , "Generate Btwn(x, y) atoms in produced formulas, for use in GRASShopper."
                , fun _ -> insertBtwns := true)
            .Add( "model="
                , "Timestamp of trained model to use (to use data/model-<TIMESTAMP>/ pass <TIMESTAMP> to this) [default: most recent]."
                , fun (s: string) -> modelName := s)
            .Add( "debug"
                , "Show debug trace of prediction."
                , fun _ -> debug := true)
            .Add( "debugger"
                , "Launch debugger to attach to this process."
                , fun _ -> System.Diagnostics.Debugger.Launch() |> ignore)
            |> ignore
    let remainingArguments = optionSet.Parse arguments |> List.ofSeq

    let dataConfiguration = new DataConfiguration(!dataDir, !tfDir, !numVars, !dsDepth, !statesPerFormula)
    let rng = System.Random(42);

    if !modelName = "" && Directory.Exists(dataConfiguration.ModelParamsDir) then
        match Directory.GetDirectories(dataConfiguration.ModelParamsDir) with
        | [||] -> printfn "Warning: no trained model found."
        | models ->
            modelName := models |> Array.map Path.GetFileName |> Array.max
    if !debug then printfn "Using trained model %s" !modelName

    match !runMode with
        | Help -> optionSet.WriteOptionDescriptions(System.Console.Error, false)
        | FormulaCreation -> CreateInitialFormulas dataConfiguration
        | StateCreation ->
            let (formulaFiles, formulasToTake) =
                if List.isEmpty remainingArguments then
                    let allFormulaFiles = Directory.GetFiles(dataConfiguration.FormulaDirectory)
                    KnuthShuffle rng allFormulaFiles
                    let numberToTake = int <| (float allFormulaFiles.Length) * !sample
                    (allFormulaFiles, numberToTake)
                else
                    let formulaFiles = remainingArguments |> Array.ofList
                    (formulaFiles, formulaFiles.Length)
            CreateStates dataConfiguration !generateGNNData formulaFiles formulasToTake
        | DatasetCreation ->
            let stateSetFiles =
                if List.isEmpty remainingArguments then
                    IO.Directory.GetFiles(dataConfiguration.StateSetDirectory)
                else
                    remainingArguments |> Array.ofList
            CreateDataset dataConfiguration 0.2 0.2 !groupSize rng stateSetFiles !sample !generateGNNData
        | DatasetCombination ->
            CombinePartialDatasetData dataConfiguration
        | ModelTraining -> TrainModel dataConfiguration
        | ModelEvaluation -> MLEvaluator.EvaluateMLModel dataConfiguration !modelName !temperature rng !groupSize !numberOfPredictions
        | ProgramRunner programFile -> RunProgram programFile !dataDir rng
        | SerializedStatePrediction -> PredictHeapDescriptionFromSerializedState dataConfiguration !modelName !temperature !numberOfPredictions remainingArguments !debug
        | GHPStatePrediction -> PredictHeapDescriptionFromGHPState dataConfiguration !modelName !temperature !numberOfPredictions remainingArguments !insertBtwns !debug
        | DatasetStatePrediction stateName -> PredictHeapDescriptionFromDatasetState dataConfiguration !modelName !temperature !groupSize !numberOfPredictions stateName rng !debug
        | DisjunctivePrediction -> PredictDisjunctiveHeapDescription dataConfiguration !modelName !temperature remainingArguments !insertBtwns !debug
        | Query -> queryMode dataConfiguration !modelName !temperature !numberOfPredictions !insertBtwns !debug

    0
