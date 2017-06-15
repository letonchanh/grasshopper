module ProgramEval

open Program
open State

let rec private evalIExpr (expr: IExpr) (state: State) (pnrg : System.Random) =
    match expr with
    | Nondet(lowerE, upperE) -> bigint(pnrg.Next(int (evalIExpr lowerE state pnrg), int (evalIExpr upperE state pnrg)))
    | Const(i) -> i
    | Neg(e1) -> 
        let v = evalIExpr e1 state pnrg
        bigint(-1) * v
    | Add(e1, e2)
    | Sub(e1, e2)
    | Mul(e1, e2) ->
        let v1 = evalIExpr e1 state pnrg
        let v2 = evalIExpr e2 state pnrg
        match expr with 
        | Add(_,_) -> v1 + v2
        | Sub(_,_) -> v1 - v2
        | Mul(_,_) | _ -> v1 * v2
    | Var(v) -> 
        match v with
        | StackVar(varName) -> (state.varStack.Get varName).GetValInt()
        | HeapVar(varName, indexExpr) -> (findAddr varName indexExpr state pnrg |> state.heap.get).GetValInt()

and private findAddr (varName: VarName) (indexExpr: IExpr) (state: State) (pnrg : System.Random) =
    let baseAddr = (state.varStack.Get varName).GetValAddr()
    let indexVal = evalIExpr indexExpr state pnrg
    baseAddr + indexVal

let rec private evalBExpr (expr: BExpr) (state: State) (pnrg : System.Random) =
    match expr with
    | Not(e1) ->
        let c1 = evalBExpr e1 state pnrg
        not(c1)
    | And(e1, e2) -> 
        let c1 = evalBExpr e1 state pnrg
        let c2 = evalBExpr e2 state pnrg
        c1 && c2
    | Or(e1, e2) -> 
        let c1 = evalBExpr e1 state pnrg
        let c2 = evalBExpr e2 state pnrg
        c1 || c2
    | Eq(e1, e2)
    | Ne(e1, e2)
    | Lt(e1, e2)
    | Le(e1, e2)
    | Gt(e1, e2)
    | Ge(e1, e2) ->
        let v1 = evalIExpr e1 state pnrg
        let v2 = evalIExpr e2 state pnrg
        match expr with
        | Eq(_,_) -> v1 = v2
        | Ne(_,_) -> v1 <> v2
        | Lt(_,_) -> v1 < v2
        | Le(_,_) -> v1 <= v2
        | Gt(_,_) -> v1 > v2
        | Ge(_,_) | _ -> v1 >= v2

let private assignValue (var: Var) (state: State) (pnrg : System.Random) (value: Value) =
    match var with
    | StackVar(varName) -> 
        state.varStack.Set varName value
    | HeapVar(varName, indexExpr) ->
        let addr = findAddr varName indexExpr state pnrg
        state.heap.set addr value

///Sets up stack for fresh call of a method, setting every argument to 0
let private setupStartState (m: Method) =
    State.empty (Method.collectVariables m)

///Sets up new stack of a called method, evaluating argument expressions to set parameters
let private setupCalledState (newMeth: Method) (args: IExpr list) (curState: State) (pnrg : System.Random) =
    let newState = { varStack = VarStack.empty (Method.collectVariables newMeth) ; heap = curState.heap }
    List.zip newMeth.parameters args 
        |> List.iter (fun (varName, e) -> ValInt (evalIExpr e curState pnrg) |> newState.varStack.Set varName)
    newState

let private dumpState (id: Program.DumpId) (state: State) (dumpInfo : IOUtils.DumpInfo) : unit =
    let idCounter = dumpInfo.NextCounter id
    let filename = sprintf "state_%s-%i_serialized.xml.gz" id idCounter
    IOUtils.SerializeData (System.IO.Path.Combine(dumpInfo.Directory.FullName, filename)) state
    dumpInfo.NoteDumpFile filename

/// Only keep heap graphs as (training) states, remove parameters of main method
let private removeParamVars (dumpVariables: VarName Set) (state: State) = 
    let newState = { varStack = VarStack.empty (dumpVariables) ; heap = state.heap }
    for varname in dumpVariables do newState.varStack.Set varname (state.varStack.Get varname)
    newState

let rec private evalStmts (p: Program) (statements: Statement list) (dumpVariables: VarName Set) (state: State) (dumpInfo : IOUtils.DumpInfo) (pnrg : System.Random) : Value =
    match statements with
    | Assign(var, expr)::rstmts ->
        ValInt (evalIExpr expr state pnrg) |> assignValue var state pnrg
        evalStmts p rstmts dumpVariables state dumpInfo pnrg
    | Malloc(var, expr)::rstmts ->
        let size = evalIExpr expr state pnrg
        let newAddr = state.heap.malloc size
        ValAddr newAddr |> assignValue var state pnrg
        evalStmts p rstmts dumpVariables state dumpInfo pnrg
    | Call(var, methodName, args)::rstmts ->
        try
            let newMethod = p.findMethod methodName
            let newState = setupCalledState newMethod args state pnrg
            let returnVal = evalMethod p newMethod newState dumpInfo pnrg
            returnVal |> assignValue var state pnrg
            evalStmts p rstmts dumpVariables state dumpInfo pnrg
        with
        | :? System.Collections.Generic.KeyNotFoundException ->
            eprintfn "Could not find method %s!" methodName
            p.methods |> List.iter (fun m -> eprintfn " Known method: %s" m.name)
            exit -1
    | Return(expr)::_ ->
        evalIExpr expr state pnrg |> ValInt
    | If(cond, ifStmts, elseStmts)::rstmts ->
        if evalBExpr cond state pnrg then
            evalStmts p (ifStmts@rstmts) dumpVariables state dumpInfo pnrg
        else
            evalStmts p (elseStmts@rstmts) dumpVariables state dumpInfo pnrg
    | While(cond, bodyStmts)::rstmts ->
        if evalBExpr cond state pnrg then
            evalStmts p (bodyStmts@statements) dumpVariables state dumpInfo pnrg
        else
            evalStmts p rstmts dumpVariables state dumpInfo pnrg
    | DumpState(id)::rstmts ->
        // skip parameters of methods, and only save dumped variables, e.g., list as in "dumpState list"
        let stateToDump = state |> removeParamVars dumpVariables

        dumpState id stateToDump dumpInfo
        evalStmts p rstmts dumpVariables state dumpInfo pnrg
    | [] -> ValInt bigint.Zero
and private evalMethod (p: Program) (m: Method) (state: State) (dumpInfo : IOUtils.DumpInfo) (pnrg : System.Random) : Value =
    let dumpVariables = Set.unionMany(List.map Statement.collectVariables m.body)
    evalStmts p m.body dumpVariables state dumpInfo pnrg

let public eval (p:Program) (dumpInfo: IOUtils.DumpInfo) (pnrg : System.Random) (paramValues: int list) =
    let mainMethod = p.findMethod "main"
    let state = setupStartState mainMethod
    let mainParameters = mainMethod.parameters
    for varName, value in Seq.zip mainParameters paramValues do
        assignValue (StackVar(varName)) state pnrg (bigint(value) |> ValInt)
        printf "%s=%i " varName value

    let _ = evalMethod p mainMethod state dumpInfo pnrg

    state