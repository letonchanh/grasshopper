module Program

type VarName = string
type MethodName = string
type DumpId = string

type Var = 
    | StackVar of VarName
    | HeapVar of VarName * IExpr

    override self.ToString () =
        match self with
        | StackVar(v) -> v
        | HeapVar(v, e) -> v.ToString() + "[" + e.ToString() + "]"
and
    IExpr =
    | Nondet of IExpr * IExpr
    | Const of bigint
    | Var of Var
    | Neg of IExpr 
    | Add of IExpr * IExpr | Sub of IExpr * IExpr | Mul of IExpr * IExpr

    override self.ToString () = 
        let protect s f e = if s >= f then e else "(" + e + ")"
        let rec pp f self =
            match self with
            | Nondet(l, u)-> sprintf "nondet(%s, %s)" (pp 0 l) (pp 0 u)
            | Const(bi)   -> bi.ToString()
            | Var(v)      -> v.ToString()
            | Neg(e)      -> "-" + pp 3 e
            | Add(e1, e2) -> protect 1 f ((pp 1 e1) + "+" + (pp 1 e2))
            | Sub(e1, e2) -> protect 1 f ((pp 1 e1) + "-" + (pp 2 e2))
            | Mul(e1, e2) -> protect 2 f ((pp 2 e1) + "*" + (pp 2 e2))
        pp 0 self

type BExpr =
    | Not of BExpr 
    | And of BExpr * BExpr | Or of BExpr * BExpr 
    | Eq of IExpr * IExpr | Ne of IExpr * IExpr | Lt of IExpr * IExpr | Le of IExpr * IExpr | Ge of IExpr * IExpr | Gt of IExpr * IExpr

    override self.ToString() =
        let protect s f e = if s >= f then e else "(" + e + ")"

        // using standard C precedence
        let rec pp f self =
            match self with
            | Not(e)     -> protect 3 f ("not " + pp 3 e)
            | And(e1,e2) -> protect 2 f (pp 2 e1 + " && " + pp 2 e2)
            | Or(e1,e2)  -> protect 1 f (pp 1 e1 + " || " + pp 1 e2)
            | Eq(e1,e2)  -> e1.ToString() + " == " + e2.ToString()
            | Ne(e1,e2)  -> e1.ToString() + " != " + e2.ToString()
            | Lt(e1,e2)  -> e1.ToString() + " < " + e2.ToString()
            | Le(e1,e2)  -> e1.ToString() + " <= " + e2.ToString()
            | Ge(e1,e2)  -> e1.ToString() + " >= " + e2.ToString()
            | Gt(e1,e2)  -> e1.ToString() + " > " + e2.ToString()
        pp 0 self

type Statement =
    | Assign of Var * IExpr
    | Malloc of Var * IExpr
    | Call of Var * MethodName * IExpr list
    | Return of IExpr
    | While of BExpr * Statement list
    | If of BExpr * Statement list * Statement list
    | DumpState of DumpId

    member self.pp (prefix: string) =
        let newline = System.Environment.NewLine
        let res = 
            match self with
            | Assign(v, e) -> sprintf "%s%s := %s;" prefix (v.ToString()) (e.ToString())
            | Malloc(v, e) -> sprintf "%s%s := malloc(%s);" prefix (v.ToString()) (e.ToString())
            | Call(v, m, args) ->
                let argList = args |> List.map (fun v -> v.ToString()) |> String.concat ", "
                sprintf "%s%s := %s(%s);" prefix (v.ToString()) m argList
            | Return(e) -> sprintf "%sreturn %s;" prefix (e.ToString())
            | While(c, b) ->
                let b_res = b |> Seq.map (fun s -> s.pp (prefix + "  ")) |> String.concat ""
                (sprintf "%swhile (%s) {%s" prefix (c.ToString()) newline) + b_res + prefix + "}"
            | If(c, t, e) ->
                let t_res = t |> Seq.map (fun s -> s.pp (prefix + "  ")) |> String.concat ""
                if (e.IsEmpty) then
                    (sprintf "%sif (%s) {%s" prefix (c.ToString()) newline) + t_res + prefix + "}"
                else
                    let e_res = e |> Seq.map (fun s -> s.pp (prefix + "  ")) |> String.concat ""
                    (sprintf "%sif (%s) {%s" prefix (c.ToString()) newline) + e_res + prefix + "} else {" + newline + e_res + prefix + "}"
            | DumpState(i) -> sprintf "%sdumpState %s;" prefix i
        res + newline

    override self.ToString() =
        self.pp ""

    static member collectVariables stmt =
        match stmt with
        | Assign (StackVar(v), _) 
        | Assign (HeapVar(v, _), _)
        | Malloc (StackVar(v), _)
        | Malloc (HeapVar(v, _), _) 
        | Call (StackVar(v), _, _)
        | Call (HeapVar(v, _), _, _) -> Set.singleton v
        | While (_, stmts) -> Set.unionMany (List.map Statement.collectVariables stmts)
        | If (_, stmts1, stmts2) ->  Set.unionMany (List.map Statement.collectVariables (stmts1@stmts2))
        | Return _
        | DumpState _  -> Set.empty

type Method = {
        name : MethodName;
        parameters : VarName list;
        body: Statement list;
    }
    with
        override self.ToString() =
            let argList = self.parameters |> List.map (fun v -> v.ToString()) |> String.concat ", "
            let stmtList = self.body |> List.map (fun s -> s.pp "  ") |> String.concat ""
            sprintf "%s(%s) {%s%s}%s" self.name argList System.Environment.NewLine stmtList System.Environment.NewLine

        static member collectVariables meth =
            Set.unionMany ((Set.ofSeq meth.parameters) :: (List.map Statement.collectVariables meth.body))
    end

type Program = {
        methods : Method list;
    }
    with
        override self.ToString() =
            let rec pp = function
                | (m::ms) -> sprintf "%s%s%s" (m.ToString()) System.Environment.NewLine (pp ms)
                | [] -> ""
            pp self.methods

        member self.findMethod (n: MethodName) =
            try
                List.find (fun m -> m.name = n) self.methods
            with
            | :? System.Collections.Generic.KeyNotFoundException ->
                eprintfn "Cannot find definition of method '%s'." n
                exit -1
    end