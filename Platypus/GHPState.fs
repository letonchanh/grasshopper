module GHPState

open Utils
open State

let parse fileName =
    use inchan = new System.IO.StreamReader (System.IO.File.OpenRead fileName)
    let lexbuf = Microsoft.FSharp.Text.Lexing.LexBuffer<char>.FromTextReader inchan
    let (varInfo, heapEdges) = GHPStateParse.ghpState GHPStateFlex.token lexbuf
    inchan.Close();

    let varStack = State.VarStack.empty (List.map fst varInfo |> Set.ofList)
    varInfo |> List.iter (fun (var, value) -> varStack.Set var value)

    let heapGraph = MutableGraph()
    for (source, field, target) in heapEdges do
        match target with
        | ValAddr targetAddr ->
            let fieldIntId = Utils.GetIdForFieldName field
            heapGraph.AddEdge source (HeapLabel fieldIntId) targetAddr
        | ValInt _ ->
            ()

    (varStack, heapGraph)
