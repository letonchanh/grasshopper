module IOUtils

open System.IO
open System.IO.Compression
open System.Runtime.Serialization
open Utils

type DataSetType =
    | Training
    | Validation
    | Test

    override self.ToString() =
        match self with
        | Training   -> "train"
        | Validation -> "val"
        | Test       -> "test"

//////////////////////////////////////// Working with (gzipped) files, serialization:
/// Gets an output stream for a given filename (gziped, if indicated by name). User is responsible for disposal.
let GetOutStream fileName : Stream =
    let fileInfo = FileInfo(fileName)
    fileInfo.Directory.Create()
    let outStream = fileInfo.Create()
    if fileName.EndsWith(".gz") then
        new GZipStream(outStream, Compression.CompressionLevel.Fastest) :> _
    else
        outStream :> _

/// Gets an input stream for a given filename (gziped, if indicated by name). User is responsible for disposal.
let GetInStream fileName : Stream =
    let fileInfo = FileInfo(fileName)
    if not(fileInfo.Exists) then
        eprintfn "File %s does not exist." (fileInfo.FullName)
        raise (FileNotFoundException())
    let inStream = fileInfo.OpenRead()
    if fileName.EndsWith(".gz") then
        new GZipStream(inStream, CompressionMode.Decompress) :> _
    else
        inStream :> _

let SerializeData fileName data =
    use outStream = GetOutStream fileName
    let formatter = NetDataContractSerializer()
    formatter.Serialize(outStream, box data)
    ()

let DeserializeData fileName =
    use uncompressedInStream = GetInStream fileName
    let formatter = NetDataContractSerializer()
    let res = formatter.Deserialize(uncompressedInStream)
    uncompressedInStream.Close()
    unbox res

/// If directory dirName exists, then delete it
let CleanDirectory dirName =
    let dataDir = System.IO.DirectoryInfo(dirName)
    if dataDir.Exists then
        dataDir.Delete(true)

type OutputStreamCache() =
    let filenameToFileHandle = new System.Collections.Concurrent.ConcurrentDictionary<string, System.IO.StreamWriter>()
    member __.GetOutputStream fileName =
        filenameToFileHandle.GetOrAdd
            (fileName,
             fun fileName -> new System.IO.StreamWriter(GetOutStream fileName))

    interface System.IDisposable with
        member __.Dispose () =
            filenameToFileHandle |> Seq.iter (fun kv -> kv.Value.Dispose())

type DumpInfo =
    {
        Directory : DirectoryInfo;
        mutable DumpIdToCounter : Map<Program.DumpId, int>;
        mutable DumpedFiles : string list;
    }
    member self.NextCounter (id : Program.DumpId) =
        let newCounter = 1 + Map.FindWithDefault id 0 self.DumpIdToCounter
        self.DumpIdToCounter <- self.DumpIdToCounter |> Map.add id newCounter
        newCounter
    member self.NoteDumpFile (f : string) =
        self.DumpedFiles <- f :: self.DumpedFiles

let SaveExistentialMaps (outFilePath : string) (exVars: Map<string, bigint>) (subheapStartToExAddr: ListDictionary<bigint, bigint>) =
    use outStream = new StreamWriter(GetOutStream outFilePath)
    outStream.WriteLine("-1:{0}", exVars |> Map.toSeq |> Seq.sortBy fst |> Seq.map (snd >> string) |> String.concat ",")
    for (start, existentials) in subheapStartToExAddr do
        outStream.WriteLine("{0}:{1}", start, existentials |> List.map string |> String.concat ",")

let LoadExistentialMaps (inFilePath : string) =
    use inStream = new StreamReader(GetInStream(inFilePath))
    let inFileInfo = FileInfo inFilePath
    let subheapStartToExAddr = ListDictionary()
    while not inStream.EndOfStream do
        let line = inStream.ReadLine()
        if line.Contains ":" then
            let lineSplit = line.Split ':'
            if lineSplit.Length > 2 then
                failwith (sprintf "Map line in '%s' with unexpected format:\n  '%s'" inFileInfo.Name line)
            else
                let mappedAddr = System.Numerics.BigInteger.Parse lineSplit.[0]
                let values =
                    if lineSplit.[1].Length > 0 then
                        lineSplit.[1].Split ',' |> Array.map System.Numerics.BigInteger.Parse |> List.ofArray
                    else
                        []
                subheapStartToExAddr.[mappedAddr] <- values
        else
            failwith (sprintf "Line in '%s' with unexpected format:\n  '%s'" inFileInfo.Name line)
    subheapStartToExAddr

/// Representation of parameters in our dataset, and the corresponding file system structure.
type DataConfiguration(dataDir : string, tfDir: string, numberOfVariables : int, dataStructureNestDepth : int, numberOfHeapsPerFormula : int) =
    member __.DataDir with get () = dataDir
    member __.TfDir with get() = tfDir
    member __.NumberOfVariables with get () = numberOfVariables
    member __.DataStructureNestDepth with get () = dataStructureNestDepth
    member __.NumberOfHeapsPerFormula with get () = numberOfHeapsPerFormula

    /// Directory for serialized formulas
    member __.FormulaDirectory
        with get () =
            Path.Combine(dataDir,
                         sprintf "%ivars_%inesting" numberOfVariables dataStructureNestDepth,
                         "formulas")

    /// Filename for a serialized formula
    member self.FormulaFile
        with get formulaIndex =
            Path.Combine(self.FormulaDirectory,
                         sprintf "formula_%i.xml.gz" formulaIndex)

    /// Directory for a certain number of generated concrete states
    member __.StateSetDirectory
        with get () =
            Path.Combine(dataDir,
                         sprintf "%ivars_%inesting" numberOfVariables dataStructureNestDepth,
                         sprintf "%istates" numberOfHeapsPerFormula)

    /// Filename for serialized lists of generated concrete states
    member self.StateSetFile
        with get formulaIndex =
            Path.Combine(self.StateSetDirectory,
                         sprintf "formula_%i_states.xml.gz" formulaIndex)

    //////////////////////////////////////// Directory and file names for the generated dataset:
    /// Directory name for a training/test/validation dataset
    member __.DatasetDir
        with get () =
            Path.Combine(dataDir,
                         sprintf "%ivars_%inesting" numberOfVariables dataStructureNestDepth,
                         sprintf "dataset_%istates" numberOfHeapsPerFormula)


    /// Directory name for a training/test/validation dataset part
    member self.DatasetPartDir
        with get dataSetType = Path.Combine(self.DatasetDir, dataSetType.ToString())

    /// Filename for the textual representation of a formula in a dataset
    member self.FormulaTextFilePath
        with get (dataSetType, formulaId) =
            (Path.Combine(self.DatasetPartDir dataSetType,
                          "formula_" + string formulaId + ".txt"))
    static member FormulaIdRegularExpression
        with get () =
            System.Text.RegularExpressions.Regex @"formula_(\d+).txt"

    /// Filename for the textual representation of a state in a dataset
    member self.StateTextFilePath
        with get (dataSetType, formulaId, heapId) =
            Path.Combine((self.FormulaTextFilePath (dataSetType, formulaId)) + "_states",
                         "state_" + string heapId + ".txt")
    static member StateIdRegularExpression
        with get () =
            System.Text.RegularExpressions.Regex @"state_(\d+).txt"

    /// Filename for the textual representation of existentials in a dataset
    member self.ExistentialMapTextFilePath
        with get (dataSetType, formulaId, heapId) =
            let stateFile = FileInfo(self.StateTextFilePath (dataSetType, formulaId, heapId))
            System.IO.Path.Combine(stateFile.DirectoryName, "existentials_" + stateFile.Name)

    //////////////////////////////////////// Directory and file names for the generated data for our machine learning models:
    /// Directory name for the machine learning training data
    member __.MLDataDir
        with get () =
            Path.Combine(dataDir,
                         sprintf "%ivars_%inesting" numberOfVariables dataStructureNestDepth,
                         "modelTraining")

    /// Filename for the serialized store of per-nonterminal mappings from numeric IDs (used for multi-class classification) to productions (used for syntax trees)
    member self.ProductionStoreFile
        with get () =
            Path.Combine(self.MLDataDir, "productionStore.xml.gz")

    /// Filename for the serialized map of features to feature indices in our dataset
    member self.FeatureToFeatureIndexMapFile
        with get () =
            Path.Combine(self.MLDataDir, "featureToFeatureIndex.xml.gz")

    /// Filename for the serialized map of features to feature indices in our dataset
    member self.NonterminalFeatureToFeatureIndexMapFile
        with get nonterminal =
            Path.Combine(self.MLDataDir,
                         sprintf "%sFeatureToFeatureIndex.xml.gz" nonterminal)

    /// Filename of the CSV file that we use to communicate with external tools (TLC, custom neural network implementation)
    member self.DataSetFile
        with get (dataSetType, nonterminal) =
            let extension = ""
            //if dataSetType <> DataSetType.Training || nonterminal = "addr"  || nonterminal.StartsWith "expr" then ".gz" else ""
            Path.Combine(self.MLDataDir,
                         sprintf "%s_%s_data.csv%s" (dataSetType.ToString()) nonterminal extension)

    /// Filename of the file containing meta info for the external tools (TF, custom neural network implementation)
    member self.MetaInfoFile
        with get () =
            Path.Combine(self.MLDataDir,
                         "metadata.csv")

    member self.PartialDataSetDir
        with get () =
            Path.Combine(self.MLDataDir, "partial")

    /// Filename of the CSV file that contains partial results which we will combine and then pass to external tools
    member self.PartialDataSetFile
        with get (dataSetType, formulaId, nonterminal) =
            Path.Combine(self.PartialDataSetDir,
                         sprintf "%s_%s_%i_data.csv.gz" (dataSetType.ToString()) nonterminal formulaId)
    member __.PartialDataSetFilePattern
        with get (dataSetType, nonterminal) =
            sprintf "%s_%s_*_data.csv.gz" (dataSetType.ToString()) nonterminal
    static member PartialDataSetFileRegularExpression
        with get () =
            System.Text.RegularExpressions.Regex @"([^_]+)_([^_]+)_([^_]+)_data.csv.gz"

    /// Filename for the serialized partial store of per-nonterminal mappings from numeric IDs (used for multi-class classification) to productions (used for syntax trees)
    member self.PartialProductionStoreFile
        with get (dataSetType, formulaId) =
            Path.Combine(self.PartialDataSetDir,
                         sprintf "%s_productionStore_%i.xml.gz" (dataSetType.ToString()) formulaId)

    member self.PartialDataSetUsedNonterminalDir
        with get () =
            Path.Combine(self.MLDataDir, "partial", "nonterminals")

    member self.PartialDataSetUsedNonterminalFile
        with get nonterminal =
            Path.Combine(self.PartialDataSetUsedNonterminalDir, nonterminal + ".gz")

    member self.PartialDataSetUsedExprDir
        with get () =
            Path.Combine(self.MLDataDir, "partial", "expressions")

    //////////////////////////////////////// Directory and file names for parameters of trained ML models
    /// Directory for the trained model data
    member self.ModelParamsDir
        with get () =
            Path.Combine(dataDir, "models")

    /// This trained model's copy of production store file
    member self.ModelProductionStoreFile
        with get modelName =
            Path.Combine(self.ModelParamsDir, modelName, "productionStore.xml.gz")

    /// Filename for this trained model's copy of serialized map of features to feature indices
    member self.ModelFeatureToFeatureIndexMapFile
        with get modelName =
            Path.Combine(self.ModelParamsDir, modelName, "featureToFeatureIndex.xml.gz")

    /// Filename for this trained model's copy of serialized map of features to feature indices
    member self.ModelNonterminalFeatureToFeatureIndexMapFile
        with get (nonterminal, modelName) =
            Path.Combine(self.ModelParamsDir, modelName,
                         sprintf "%sFeatureToFeatureIndex.xml.gz" nonterminal)

    //////////////////////////////////////// Directory and file names for specific predictors:
    /// Filename for the mapping from label indices to strings for a chosen predictor variation and nonterminal
    member self.PredictorFile
        with get (predictorName, variation, nonterminal) =
            FileInfo(Path.Combine(self.MLDataDir,
                                      "predictors",
                                      sprintf "%s-%s" predictorName variation,
                                      sprintf "%s.model" nonterminal))

    /// Base path for the neural networks trained for scoring expression production candidates
    member self.ExpressionNeuralNetBasePath
        with get exprPosId =
            Path.Combine(self.MLDataDir,
                         "predictors",
                         sprintf "%s_NeuralNet" exprPosId)

    /// Base path for the neural networks trained for scoring candidates for existential quantification
    member self.ExistentialNeuralNetBasePath
        with get () =
            Path.Combine(self.MLDataDir,
                         "predictors",
                         "addr_NeuralNet")

    //////////////////////////////////////// Directory and file names for evaluation data
    member __.EvaluationResultForThread
        with get threadId =
            Path.Combine(dataDir,
                         sprintf "%ivars_%inesting" numberOfVariables dataStructureNestDepth,
                         sprintf "eval-data-%i.gz" threadId)

    member __.EvaluationResult
        with get (predictions, batchSize) =
            Path.Combine(dataDir,
                         sprintf "%ivars_%inesting" numberOfVariables dataStructureNestDepth,
                         sprintf "evaluation-results-%ipreds-%ibatchSize.txt.gz" predictions batchSize)

    //////////////////////////////////////// Directory and file names for graph property datasets:
    member self.GraphPropertyDatasetZip
        with get () =
            Path.Combine(self.DataDir, "graphPropertyData.zip")

    //////////////////////////////////////// Directory and file names for clustering datasets:
    member __.ClusteringDatasetFile
        with get () =
            Path.Combine(dataDir,
                         sprintf "%ivars_%inesting" numberOfVariables dataStructureNestDepth,
                         "clusteringDataset.xml.gz")
    member __.ClusteringCacheFile
        with get (instanceId) =
            Path.Combine(dataDir,
                         sprintf "%ivars_%inesting" numberOfVariables dataStructureNestDepth,
                         "clustering_caches",
                         instanceId.ToString())
