module MLEvaluator

open System
open System.IO

open FSharp.Collections.ParallelSeq

open Utils
open Predictor
open DataSet

type PrecisionInformation =
    {
        NonterminalToPredictionNumber : Map<string, int>

        NonterminalToCorrectPredictionNumber : Map<string, int>

        /// Ratio of cases where the first (1, 2, ...) predictions contained the ground truth
        PrecisionAtKPredictions : float list
    }

    member self.GetPrecisionForNonterimal nonterminal =
        let total = Map.FindWithDefault nonterminal 0 self.NonterminalToPredictionNumber
        let correct = Map.FindWithDefault nonterminal 0 self.NonterminalToCorrectPredictionNumber
        (float total) / (float correct)


type EvaluationResult =
    {
        DataConfiguration : IOUtils.DataConfiguration
        GroupSize : int

        TraininingData : PrecisionInformation
        TestData : PrecisionInformation
    }

    member self.ToOutStream outStream =
        let newLine = System.Environment.NewLine
        let tableLineFormat = "|{0,-25}|{1,-10:F02}|{2,-10:F02}|"
        let tableRowSep = String('-', String.Format(tableLineFormat, "", "", "", "").Length)

        ///// Print metadata about the experiment:
        fprintfn outStream "Config: #Var: %i; nestDepth: %i; #States/formula: %i; groupSize:%i"
            self.DataConfiguration.NumberOfVariables self.DataConfiguration.DataStructureNestDepth self.DataConfiguration.NumberOfHeapsPerFormula
            self.GroupSize
        fprintfn outStream "Model: Tensorflow"

        ///// Print precision per syntax tree
        fprintfn outStream "%sPrecision for full syntax trees:" newLine
        fprintfn outStream "    %s" tableRowSep
        fprintfn outStream "    %s" (String.Format(tableLineFormat, "Precision @ K", "train", "test1", "test2"))
        fprintfn outStream "    %s" tableRowSep
        let combinedPrecisions = List.zip self.TraininingData.PrecisionAtKPredictions self.TestData.PrecisionAtKPredictions
        for (k, (trainingPrecision, testPrecision)) in combinedPrecisions |> List.mapi (fun i e -> (i + 1, e)) do
            fprintfn outStream "    %s" (String.Format(tableLineFormat, k, trainingPrecision, testPrecision))
            fprintfn outStream "    %s" tableRowSep

        ///// Print precision per nonterminal:
        fprintfn outStream "%s%sPrecision per nonterminal:" newLine newLine
        fprintfn outStream "    %s" tableRowSep
        fprintfn outStream "    %s" (String.Format(tableLineFormat, "Precision/nonterminal", "train", "test1", "test2"))
        fprintfn outStream "    %s" tableRowSep
        for nonterminal in self.TraininingData.NonterminalToPredictionNumber.Keys do
            let trainPrecisionForNonterminal = self.TraininingData.GetPrecisionForNonterimal nonterminal
            let testPrecisionForNonterminal = self.TestData.GetPrecisionForNonterimal nonterminal
            fprintfn outStream "    %s" (String.Format(tableLineFormat, nonterminal, trainPrecisionForNonterminal, testPrecisionForNonterminal))
            fprintfn outStream "    %s" tableRowSep

let SaveEvalResults (dataConfiguration : IOUtils.DataConfiguration) (evalRes : EvaluationResult) modelName =
    let outFile = FileInfo(Path.Combine(dataConfiguration.DataDir, "EvaluationResults", sprintf "%s-output.txt" modelName))
    printfn "Saving output to file %s" outFile.FullName
    outFile.Directory.Create()
    use outStreamRes = outFile.CreateText()
    evalRes.ToOutStream outStreamRes

let ComputePrecisionPerState (dataConfiguration : IOUtils.DataConfiguration) modelName temperature (dataSet : DataSet) numPredictionsPerState =
    let totalNum = dataSet.GetInstanceNumber ()

    printfn "Looking at %i test data instances" totalNum
    use streamCache = new IOUtils.OutputStreamCache()
    let threadLocalData : System.Collections.Concurrent.ConcurrentDictionary<int, PredictionEvaluationInformation> = System.Collections.Concurrent.ConcurrentDictionary()
    let threadlocalML: Collections.Concurrent.ConcurrentDictionary<int, MLWrapper.SoftmaxModelWrapper> = Collections.Concurrent.ConcurrentDictionary()
    let testOneExample dataSetElement =
        //Get the thread-local data:
        let threadId = System.Threading.Thread.CurrentThread.ManagedThreadId
        let evalInfo = threadLocalData.GetOrAdd (threadId, fun _ -> PredictionEvaluationInformation(numPredictionsPerState))
        let outStream = streamCache.GetOutputStream (dataConfiguration.EvaluationResultForThread threadId)
        let mlwrapper = threadlocalML.GetOrAdd(threadId, fun _ -> new MLWrapper.SoftmaxModelWrapper(dataConfiguration, modelName, temperature))

        // Reset rng for every example
        evalInfo.RNG <- System.Random(42)
        if evalInfo.ObservedTestCounter % 50 = 0 then
            printfn "(%i): %s: Formula %i, States %s, tested on %i examples" threadId (System.DateTime.Now.ToString()) dataSetElement.FormulaId (dataSetElement.StatesWithSubheapToExVars |> List.map (fst >> string) |> String.concat ", ") evalInfo.ObservedTestCounter

        //Produce predictions for this element of the test set:
        let (groundTruthSyntaxTree, _) = SyntaxTree.SyntaxTree.fromSepLogicFormula dataSetElement.Formula
        let groundTruthFormulaString = groundTruthSyntaxTree.ToCanonicalString ()
        let envsWithIds =
            dataSetElement.StatesWithSubheapToExVars |>
            List.map (fun (stateId, env) -> (env, sprintf "(%i, %i)" dataSetElement.FormulaId stateId))

        let (greedyTreeString, predictedSyntaxTrees) =
            PredictSyntaxTree mlwrapper (List.map fst envsWithIds) numPredictionsPerState true false false
        let atLeastOneCorrectPrediction = List.exists (fst >> (=) groundTruthFormulaString) predictedSyntaxTrees

        //Do evaluation of ground truth:
        let groundTruthSyntaxTreeProb =
            ("", CalculateSyntaxTreeProb mlwrapper groundTruthSyntaxTree (List.map fst envsWithIds) evalInfo false, groundTruthFormulaString)

        //Print to log:
        let orderedSyntaxTrees =
            predictedSyntaxTrees
            |> List.sortBy (fun (_, (_, p)) -> -p) //Sort by descending probability
            |> List.mapi (fun idx (treeString, (_, p)) -> (sprintf "pred %i" idx, p, treeString))

        let correctAtIndex =
            orderedSyntaxTrees
            |> List.map (fun (_, _, predictedTreeString) -> if predictedTreeString = groundTruthFormulaString then 1 else 0) //mapped to correct/not correct

        fprintfn outStream "%s: " (String.concat "," (List.map (fun (stateId, _) -> "(" + string dataSetElement.FormulaId + "," + string stateId + ")") dataSetElement.StatesWithSubheapToExVars))
        fprintfn outStream " ---------- Groundtruth / Predicted %s:" (if atLeastOneCorrectPrediction then "(+)" else "(-)")
        for (id, prob, predictedTreeString) in groundTruthSyntaxTreeProb :: orderedSyntaxTrees do
            fprintfn outStream " {p=%.4f} %s %-8s %s" prob (if predictedTreeString = groundTruthFormulaString then "(+)" else "(-)") id predictedTreeString

        //Store statistical data for the future:
        evalInfo.NoteResult dataSetElement.FormulaId atLeastOneCorrectPrediction (greedyTreeString = groundTruthFormulaString) correctAtIndex

    //Do the calls in parallel
    dataSet |> PSeq.withDegreeOfParallelism 6 |> PSeq.iter testOneExample

    //Collect partial results:
    use logFileStream = IOUtils.GetOutStream (dataConfiguration.EvaluationResult (numPredictionsPerState, dataSet.GroupSize))
    use logFileStreamWriter = new System.IO.StreamWriter(logFileStream)
    let evalInfo = PredictionEvaluationInformation(numPredictionsPerState)
    for KeyValue(threadId, threadEvalInfo) in threadLocalData do
        evalInfo.IncludeInformation threadEvalInfo

        //Copy all output into one file:
        let threadLogFile = dataConfiguration.EvaluationResultForThread threadId
        let threadOutStream = streamCache.GetOutputStream threadLogFile
        threadOutStream.Close()
        threadOutStream.Dispose()
        use inStream = IOUtils.GetInStream threadLogFile
        inStream.CopyTo logFileStream
        inStream.Close()
        (FileInfo threadLogFile).Delete()

    evalInfo.PrintSummary logFileStreamWriter

let EvaluateMLModel (dataConfiguration : IOUtils.DataConfiguration) modelName modelConfiguration rng groupSize numberOfPredictions =
    use testDataSet = new DataSet.DataSet(dataConfiguration.DatasetPartDir IOUtils.DataSetType.Test, groupSize, rng)

    ComputePrecisionPerState dataConfiguration modelName modelConfiguration testDataSet numberOfPredictions