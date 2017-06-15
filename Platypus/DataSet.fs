module DataSet

open Utils

let NewLine = System.Environment.NewLine
let SepLine = "----------------------------------"
let EmpLine = "=================================="

type DataSetElement =
    {
        FormulaId : int
        Formula : SepLogic.SymHeap
        StatesWithSubheapToExVars : (int * Features.Environment) list
    }

type DataSet (baseDirectoryPath : string, groupSize : int, rng : System.Random, formulaId : int option, stateId : int option) =
    let baseDirectory = System.IO.DirectoryInfo baseDirectoryPath
    let formulaFiles = 
        match formulaId with
        | Some formulaId -> baseDirectory.GetFiles(sprintf "formula_%i.txt" formulaId)
        | None ->           baseDirectory.GetFiles("formula_*.txt")

    let mutable currentFormulaIndex = -1
    let mutable currentStateFileList = null
    let mutable nextStateIndex = -1

    let mutable currentFormulaId = None
    let mutable currentFormula = None
    let mutable currentStateAndSubheapMaps = None

    let mutable numberCache = None

    let getStateFileList (formulaFileInfo : System.IO.FileInfo) =
        let statePattern =
            match stateId with
            | Some stateId -> sprintf "state_%i.txt" stateId
            | None         -> "state_*.txt"
        System.IO.DirectoryInfo(formulaFileInfo.FullName + "_states").GetFiles(statePattern)
    let readNextFormula () =
        //Reset counters appropriately:
        nextStateIndex <- 0
        currentFormulaIndex <- currentFormulaIndex + 1

        //Read new formula and extract ID:
        let newFormulaFile = formulaFiles.[currentFormulaIndex]
        currentFormula <- Some <| (DataSet.ReadFormulaFromFile newFormulaFile)
        let res = IOUtils.DataConfiguration.FormulaIdRegularExpression.Match newFormulaFile.Name
        assert (res.Success)
        currentFormulaId <- Some (System.Int32.Parse res.Groups.[1].Value)

        //Update list of states for that formula, and shuffle it for good measure:
        let newStateFiles = getStateFileList newFormulaFile
        KnuthShuffle rng newStateFiles
        currentStateFileList <- newStateFiles

    member __.GroupSize with get() = groupSize

    new (baseDirectoryPath : string, groupSize : int, rng : System.Random) =
        new DataSet (baseDirectoryPath, groupSize, rng, None, None)

    static member ReadFormulaFromFile formulaFile =
        use inchan = new System.IO.StreamReader (formulaFile.OpenRead())
        let lexBuf = Microsoft.FSharp.Text.Lexing.LexBuffer<char>.FromTextReader inchan
        SepLogicParse.formula SepLogicFlex.token lexBuf

    static member ReadStateInfoFromFile (stateFile : System.IO.FileInfo) : Features.Environment =
        let (varStack, heapGraph) = State.fileToStackAndHeapGraph stateFile.FullName
        let subheapStartToExVars = IOUtils.LoadExistentialMaps (System.IO.Path.Combine(stateFile.DirectoryName, "existentials_" + stateFile.Name))
        (HeapGraph(AnnotatedGraph(heapGraph), Some subheapStartToExVars), (Features.varEnvFromVarStack varStack))

    member __.GetInstanceNumber () =
        match numberCache with
        | Some n -> n
        | None ->
            let number = Array.sumBy (fun f -> (getStateFileList f).Length / groupSize) formulaFiles
            numberCache <- Some number
            number

    interface System.Collections.Generic.IEnumerator<DataSetElement> with
        member __.Current
             with get () =
                if currentFormula.IsNone then
                    raise (System.InvalidOperationException())
                else
                    { FormulaId                 = currentFormulaId.Value
                      Formula                   = currentFormula.Value
                      StatesWithSubheapToExVars = currentStateAndSubheapMaps.Value
                    }

    interface System.Collections.IEnumerator with
        member self.Current with get() = (self :> System.Collections.Generic.IEnumerator<DataSetElement>).Current :> _
        member __.MoveNext () =
            //Check if we need to move on to the next formula:
            if nextStateIndex < 0 || nextStateIndex + groupSize > currentStateFileList.Length then
                if currentFormulaIndex < formulaFiles.Length - 1 then
                    readNextFormula()
            if nextStateIndex + groupSize <= currentStateFileList.Length then
                //Read groupSize new states:
                currentStateAndSubheapMaps <-
                    Some [
                            for stateIndex in nextStateIndex .. nextStateIndex + groupSize - 1 do
                                let stateFile = currentStateFileList.[stateIndex]
                                let res = IOUtils.DataConfiguration.StateIdRegularExpression.Match stateFile.Name
                                assert (res.Success)
                                let stateId = System.Int32.Parse res.Groups.[1].Value
                                yield (stateId, DataSet.ReadStateInfoFromFile stateFile)
                         ]
                nextStateIndex <- nextStateIndex + groupSize
                true
            else
                false
        member __.Reset () =
            currentFormulaIndex <- -1
            readNextFormula()
            currentStateAndSubheapMaps <- None     

    interface System.Collections.Generic.IEnumerable<DataSetElement> with
        member self.GetEnumerator () = self :> _

    interface System.Collections.IEnumerable with
        member self.GetEnumerator () = self :> _

    interface System.IDisposable with
        member __.Dispose () = ()