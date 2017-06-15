module MLWrapper

open SyntaxTree
open Features
open System.Diagnostics
open IOUtils

[<AbstractClass>]
type ModelWrapper() =
    abstract member PredictNonterminalProductions : SparseFeatures -> Node -> STProduction [] * float []
    abstract member PredictExprProductions : string -> (bool * string * SparseFeatures) list -> string [] * float []
    abstract member ExistentialScores : (bigint * SparseFeatures) seq -> (bigint * float) []
    abstract member CloseProcess : unit -> unit
    interface System.IDisposable with
        member self.Dispose () = self.CloseProcess()

type SoftmaxModelWrapper (dataConfiguration : DataConfiguration, modelName: string, temp: float) =
    inherit ModelWrapper()
    let featuresToIndices : FeatureToIndexMap =
        DeserializeData <| dataConfiguration.ModelFeatureToFeatureIndexMapFile modelName
    let exprFiles =
        System.IO.Directory.GetFiles dataConfiguration.PartialDataSetUsedExprDir
        |> Seq.map System.IO.Path.GetFileName
    let exprToFeatureToIndices = System.Collections.Generic.Dictionary()
    do
        for exprType in Seq.append ["addr"] exprFiles do
            let exprFeatureToIndices : FeatureToIndexMap =
                DeserializeData (dataConfiguration.ModelNonterminalFeatureToFeatureIndexMapFile (exprType, modelName))
            exprToFeatureToIndices.[exprType] <- exprFeatureToIndices

    let addrFeaturesToIndices = exprToFeatureToIndices.["addr"]

    let productionStore : SyntaxTree.ProductionStore =
        DeserializeData <| dataConfiguration.ModelProductionStoreFile modelName

    let startInfo =
        ProcessStartInfo(
            FileName = "python",
            Arguments = sprintf "%s/main.py --query -m %s -t %f" dataConfiguration.TfDir
                            (System.IO.Path.Combine(dataConfiguration.ModelParamsDir, modelName))
                            temp,
            UseShellExecute = false,
            RedirectStandardOutput = true,
            RedirectStandardInput = true)
    let proc = Process.Start(startInfo)

    let queryTF (queryStr: string) =
        proc.StandardInput.Write(queryStr)
        proc.StandardInput.Flush()
        // if debug then printfn "Sent tf query: %s" queryStr

        let output = proc.StandardOutput.ReadLine()
        // if debug then printfn "Got query result: %s" output
        output.Trim()

    static member TrainAndSaveModel (dataConfiguration : DataConfiguration) =
        let startInfo =
            ProcessStartInfo(
                FileName = "python",
                Arguments = sprintf "%s/main.py --train -d %s" dataConfiguration.TfDir dataConfiguration.MLDataDir,
                UseShellExecute = false)
        let proc = Process.Start(startInfo)
        proc.WaitForExit()

    override __.ExistentialScores (addrWithFeatures : (bigint * SparseFeatures) seq) =
        let (labels, featureVectors) =
            addrWithFeatures
            |> Seq.map (fun (l, f) -> (l, f.ToFloatVector addrFeaturesToIndices))
            |> Array.ofSeq
            |> Array.unzip
        if Array.length labels > 0 then
            // Build the query
            let queryStr =
                let queryStr = System.Text.StringBuilder()
                queryStr.AppendFormat(
                    "VARIABLE {0} {1} {2}\n",
                    labels.Length,
                    "addr",
                    addrFeaturesToIndices.Count) |> ignore

                for featureVector in featureVectors do
                    featureVector
                    |> Seq.iter (fun f -> queryStr.AppendFormat("{0} ", f) |> ignore)
                    queryStr.Append("\n") |> ignore
                queryStr.ToString()

            // Query the query
            let output = queryTF queryStr

            // Build the answers
            let scores = output.Split([|' '|]) |> Array.map float

            assert (labels.Length = scores.Length)
            Array.zip labels scores
        else
            [||]

    /// Given a nonterminal node, parts of a syntax tree around it and heap graph features, predict probabilities of different production rules
    override __.PredictNonterminalProductions (features : Features.SparseFeatures) (nonterminalNode : SyntaxTree.Node) =
        let allPossibleProductions = productionStore.GetIdToProduction nonterminalNode.NodeType
        //We only built a predictor if we are facing a choice, so see if we have one:
        if allPossibleProductions.Count > 1 then
            let featureVector = features.ToFloatVector featuresToIndices

            let queryStr =
                let queryStr = System.Text.StringBuilder()
                queryStr.AppendLine("GENERIC") |> ignore
                queryStr.Append(nonterminalNode.NodeType.ToString() + " ") |> ignore
                featureVector
                |> Seq.iter (fun f -> queryStr.AppendFormat("{0} ", f) |> ignore)
                queryStr.Append("\n") |> ignore
                queryStr.ToString()
            let output = queryTF <| queryStr

            output.Split([|' '|])
            |> Array.mapi (fun i p -> (allPossibleProductions.[i], p |> float))
            |> Array.unzip
        elif allPossibleProductions.Count = 1 then
            [| (allPossibleProductions |> Seq.head).Value |], [|1.|]
        else
            failwithf "PredictNonterminalProduction got < 1 option for nonterm %O" nonterminalNode.NodeType

    override __.PredictExprProductions
            exprType
            (candidatesWithFeatures: (bool * string * Features.SparseFeatures) list) =
        // Only call the predictor if there's more than one candidate
        if candidatesWithFeatures.Length > 1 then
            // Build the query
            let queryStr =
                let queryStr = System.Text.StringBuilder()
                queryStr.AppendFormat(
                    "VARIABLE {0} {1} {2}\n",
                    candidatesWithFeatures.Length,
                    exprType,
                    exprToFeatureToIndices.[exprType].Count) |> ignore

                for _, _, features in candidatesWithFeatures do
                    let featureVector = features.ToFloatVector exprToFeatureToIndices.[exprType]
                    featureVector
                    |> Seq.iter (fun f -> queryStr.AppendFormat("{0} ", f) |> ignore)
                    queryStr.Append("\n") |> ignore
                queryStr.ToString()

            // Query the query
            let output = queryTF <| queryStr

            // Build the answers
            let idents = candidatesWithFeatures |> Seq.map (fun (_, s, _) -> s) |> Array.ofSeq
            let probs = output.Split([|' '|]) |> Array.map float

            assert (idents.Length = probs.Length)
            idents, probs
        elif candidatesWithFeatures.Length = 1 then
            let _, ident, _ = candidatesWithFeatures.Head
            [|ident|], [|1.|]
        else
            failwithf "PredictExprProductions got < 1 option for expr %O" exprType

    override __.CloseProcess () = proc.Close()
