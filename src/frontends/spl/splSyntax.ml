(** SPL abstract syntax. *)

open Grass

type idents = ident list

type pos = source_position

type name = string

type names = name list

type typ =
  | IdentType of ident
  | StructType of ident
  | MapType of typ * typ
  | ArrayType of typ
  | ArrayCellType of typ
  | SetType of typ
  | IntType
  | BoolType
  | ByteType
  | UnitType
  | AnyRefType
  | PermType (* SL formulas *)
  | AnyType

type var_decl_id =
  | IdentDecl of ident
  | ArrayDecl of var_decl_id

type spl_program =
    { includes: (name * pos) list;
      type_decls: typedecls;
      var_decls: vars;
      proc_decls: procs;
      pred_decls: preds;
      background_theory: (expr * pos) list; 
    }

and decl =
  | TypeDecl of typedecl
  | VarDecl of var
  | ProcDecl of proc
  | PredDecl of pred

and decls = decl list

and proc =
    { p_name: ident;
      p_formals: idents;
      p_returns: idents;
      p_locals: vars;
      p_contracts: contracts;
      p_body: stmt; 
      p_pos: pos;
    }

and procs = proc IdMap.t

and pred =
    { pr_name: ident;
      pr_formals: idents;
      pr_outputs: idents;
      pr_locals: vars;
      pr_contracts: contracts;
      pr_body: expr option; 
      pr_pos: pos;
    }

and preds = pred IdMap.t

and var =
    { v_name: ident;
      v_type: typ; 
      v_ghost: bool;
      v_implicit: bool;
      v_aux: bool;
      v_pos: pos;
      v_scope: pos;
    }

and vars = var IdMap.t

and typedecl =
    { t_name: ident;
      t_def: type_def;      
      t_pos: pos;
    }

and type_def =
  | FreeTypeDef
  | StructTypeDef of vars
      
and typedecls = typedecl IdMap.t
      
and contract =
  | Requires of expr * bool
  | Ensures of expr * bool

and contracts = contract list

and stmt =
  | Skip of pos
  | Block of stmts * pos
  | LocalVars of var list * exprs option * pos
  | Assume of expr * bool * pos
  | Assert of expr * bool * pos
  | Assign of exprs * exprs * pos
  | Havoc of exprs * pos
  | Dispose of expr * pos
  | If of expr * stmt * stmt * pos
  | Loop of loop_contracts * stmt * expr * stmt * pos
  | Return of exprs * pos

and stmts = stmt list

and loop_contracts = loop_contract list

and loop_contract = 
  | Invariant of expr * bool

and bound_var =
  | GuardedVar of ident * expr
  | UnguardedVar of var

and expr =
  | Null of typ * pos
  | Emp of pos
  | Setenum of typ * exprs * pos
  | IntVal of Int64.t * pos
  | BoolVal of bool * pos
  | New of typ * exprs * pos
  | Read of expr * expr * pos
  | ProcCall of ident * exprs * pos
  | PredApp of pred_sym * exprs * pos
  | Binder of binder_kind * bound_var list * expr * pos
  | UnaryOp of un_op * expr * pos
  | BinaryOp of expr * bin_op * expr * typ * pos
  | Ident of ident * pos
  | Annot of expr * annotation * pos

and exprs = expr list

and bin_op = 
  | OpDiff | OpUn | OpInt 
  | OpMinus | OpPlus | OpMult | OpDiv | OpMod 
  | OpEq | OpGt | OpLt | OpGeq | OpLeq | OpIn
  | OpPts | OpSepStar | OpSepPlus | OpSepIncl
  | OpBvAnd | OpBvOr | OpBvShiftL | OpBvShiftR 
  | OpAnd | OpOr | OpImpl 

and un_op =
  | OpArrayCells | OpIndexOfCell | OpArrayOfCell | OpLength
  | OpUMinus | OpUPlus
  | OpBvNot | OpToInt | OpToByte
  | OpNot
  | OpOld
  | OpKnown
      
and pred_sym =
  | AccessPred | BtwnPred | DisjointPred | FramePred | ReachPred | Pred of ident
      
and binder_kind =
  | Forall | Exists | SetComp

and annotation =
  | GeneratorAnnot of (expr * ident list) list * expr
  | PatternAnnot of expr
  | CommentAnnot of string

(** Utility functions *)
        
let pos_of_expr = function
  | Null (_, p) 
  | Emp p 
  | IntVal (_, p) 
  | BoolVal (_, p)
  | Setenum (_, _, p)
  | New (_, _, p)
  | Read (_, _, p)
  | Binder (_, _, _, p)
  | ProcCall (_, _, p)
  | PredApp (_, _, p)
  | UnaryOp (_, _, p)
  | BinaryOp (_, _, _, _, p)
  | Ident (_, p) -> p
  | Annot (_, _, p) -> p  

let free_vars e =
  let rec fv bv acc = function
    | Ident (x, _) ->
        if IdSet.mem x bv then acc else IdSet.add x acc
    | Setenum (_, es, _)
    | New (_, es, _)
    | ProcCall (_, es, _)
    | PredApp (_, es, _) ->
        List.fold_left (fv bv) acc es
    | UnaryOp (_, e, _)
    | Annot (e, _, _) ->
        fv bv acc e
    | Read (e1, e2, _) 
    | BinaryOp (e1, _, e2, _, _) ->
        fv bv (fv bv acc e1) e2
    | Binder (_, vs, e, _) ->
        let bv, acc =
          List.fold_left (fun (bv, acc) -> function
            | UnguardedVar v ->
                IdSet.add v.v_name bv, acc
            | GuardedVar (x, e) ->
                let acc = fv bv acc e in
                IdSet.add x bv, acc)
            (bv, acc) vs
        in
        fv bv acc e
    | _ -> acc
  in fv IdSet.empty IdSet.empty e
          
let pos_of_stmt = function
  | Skip pos
  | Block (_, pos)
  | LocalVars (_, _, pos)
  | Assume (_, _, pos)
  | Assert (_, _, pos)
  | Assign (_, _, pos)
  | Dispose (_, pos)
  | Havoc (_, pos)
  | If (_, _, _, pos)
  | Loop (_, _, _, _, pos)
  | Return (_, pos) -> pos

let proc_decl hdr body =
  { hdr with p_body = body }

let struct_decl sname sfields pos =
  { t_name = sname;  t_def = StructTypeDef sfields; t_pos = pos }

let var_decl vname vtype vghost vimpl vpos vscope =
  { v_name = vname; v_type = vtype; v_ghost = vghost; v_implicit = vimpl; v_aux = false; v_pos = vpos; v_scope = vscope } 

let pred_decl hdr body =
  { hdr with pr_body = body }

let extend_spl_program incls decls bg_th prog =
  let check_uniqueness id pos (tdecls, vdecls, pdecls, prdecls) =
    if IdMap.mem id tdecls || IdMap.mem id vdecls || IdMap.mem id pdecls || IdMap.mem id prdecls
    then ProgError.error pos ("redeclaration of identifier " ^ (fst id) ^ ".");
  in
  let tdecls, vdecls, pdecls, prdecls =
    List.fold_left (fun (tdecls, vdecls, pdecls, prdecls as decls) -> function
      | TypeDecl decl -> 
          check_uniqueness decl.t_name decl.t_pos decls;
          IdMap.add decl.t_name decl tdecls, vdecls, pdecls, prdecls
      | VarDecl decl -> 
          check_uniqueness decl.v_name decl.v_pos decls;
          tdecls, IdMap.add decl.v_name decl vdecls, pdecls, prdecls
      | ProcDecl decl -> 
          check_uniqueness decl.p_name decl.p_pos decls;
          tdecls, vdecls, IdMap.add decl.p_name decl pdecls, prdecls
      | PredDecl decl -> 
          check_uniqueness decl.pr_name decl.pr_pos decls;
          tdecls, vdecls, pdecls, IdMap.add decl.pr_name decl prdecls)
      (prog.type_decls, prog.var_decls, prog.proc_decls, prog.pred_decls)
      decls
  in
  { includes = incls @ prog.includes;
    type_decls = tdecls;
    var_decls = vdecls; 
    proc_decls = pdecls;
    pred_decls = prdecls;
    background_theory = bg_th @ prog.background_theory;
  }

let merge_spl_programs prog1 prog2 =
  let tdecls =
    IdMap.fold (fun _ decl acc -> TypeDecl decl :: acc) prog1.type_decls []
  in
  let vdecls =
    IdMap.fold (fun _ decl acc -> VarDecl decl :: acc) prog1.var_decls tdecls
  in
  let prdecls =
    IdMap.fold (fun _ decl acc -> PredDecl decl :: acc) prog1.pred_decls vdecls
  in
  let decls =
    IdMap.fold (fun _ decl acc -> ProcDecl decl :: acc) prog1.proc_decls prdecls
  in
  extend_spl_program prog1.includes decls prog1.background_theory prog2

let add_alloc_decl prog =
  let alloc_decls =
    IdMap.fold
      (fun _ decl acc ->
        match decl.t_def with
        | StructTypeDef _ ->
            let sid = decl.t_name in
            let id = Prog.alloc_id (FreeSrt sid) in
            let tpe = SetType (StructType sid) in
            let pos = GrassUtil.dummy_position in
            let scope = GrassUtil.global_scope in
            let vdecl = VarDecl (var_decl id tpe true false pos scope) in
            vdecl :: acc
        | _ -> acc)
      prog.type_decls
      []
  in
    extend_spl_program [] alloc_decls [] prog

let empty_spl_program =
  { includes = [];
    type_decls = IdMap.empty;
    var_decls = IdMap.empty;
    proc_decls = IdMap.empty;
    pred_decls = IdMap.empty;
    background_theory = [];
  }
    
let mk_block pos = function
  | [] -> Skip pos
  | [stmt] -> stmt
  | stmts -> Block (stmts, pos)

(** Utils *)

(* Visit all statements. *)
let rec stmt_iter (f : stmt -> unit) stmt =
  match stmt with
  | Block (stmts, _) -> List.iter (stmt_iter f) stmts
  | If (_, stmt1, stmt2, _) -> let _ = (stmt_iter f stmt1) in stmt_iter f stmt2
  | Loop (_, stmt1, _, stmt2, _) -> let _ = (stmt_iter f stmt1) in stmt_iter f stmt2
  | _ -> ();
  f stmt                   
                   
(** Pretty printing *)

open Format

let rec pr_type ppf = function
  | AnyRefType -> fprintf ppf "AnyRef" 
  | BoolType -> fprintf ppf "%s" bool_sort_string
  | IntType -> fprintf ppf "%s" int_sort_string
  | ByteType -> fprintf ppf "%s" byte_sort_string
  | UnitType -> fprintf ppf "Unit"
  | StructType id | IdentType id -> pr_ident ppf id
  | ArrayType e -> fprintf ppf "%s<@[%a@]>" array_sort_string pr_type e
  | ArrayCellType e -> fprintf ppf "%s<@[%a@]>" array_cell_sort_string pr_type e
  | MapType (d, r) -> fprintf ppf "%s<@[%a,@ %a@]>" map_sort_string pr_type d pr_type r
  | SetType s -> fprintf ppf "%s<@[%a@]>" set_sort_string pr_type s
  | PermType -> fprintf ppf "Permission"
  | AnyType -> fprintf ppf "Any"

let string_of_type t = pr_type str_formatter t; flush_str_formatter ()

let string_of_var_decl var =
  let modifier =
    (if var.v_implicit then "implicit " else "")
    ^ (if var.v_ghost then "ghost " else "") in
  match var.v_type with
  | AnyType ->
     Printf.sprintf "%s%s" modifier (fst var.v_name)
  | typ ->
     Printf.sprintf "%s%s : %s" modifier (fst var.v_name) (string_of_type typ)

let string_of_bin_op = function
  | OpAnd -> "&&"
  | OpOr -> "||"
  | OpIn -> "in"
  | OpImpl -> "==>"
  | OpEq -> "=="
  | OpGeq -> ">="
  | OpGt -> ">"
  | OpLt -> "<"
  | OpLeq -> "<="
  | OpSepStar -> "&*&"
  | OpSepPlus -> "&+&"
  | OpSepIncl -> "-**"
  | OpPts -> "|->"
  | OpDiff -> "--"
  | OpUn -> "++"
  | OpInt -> "**"
  | OpMinus -> "-"
  | OpPlus -> "+"
  | OpMult -> "*"
  | OpDiv -> "/"
  | OpMod -> "%"
  | OpBvAnd -> "&"
  | OpBvOr -> "|"
  | OpBvShiftL -> "<<"
  | OpBvShiftR -> ">>"

let string_of_un_op = function
  | OpUMinus -> "-"
  | OpUPlus -> "+"
  | OpNot -> "!"
  | OpBvNot -> "~"     
  | OpToInt -> "toInt"
  | OpToByte -> "toByte"
  | OpArrayCells -> failwith "string_of_unop doesn't support ArrayCells yet!"     
  | OpLength -> failwith "string_of_unop doesn't support Length yet!"
  | OpArrayOfCell -> failwith "string_of_unop doesn't support ArrayOfCell yet!"
  | OpIndexOfCell -> failwith "string_of_unop doesn't support IndexOfCell yet!"
  | OpOld -> failwith "string_of_unop doesn't support Old yet!"
  | OpKnown -> failwith "string_of_unop doesn't support Known yet!"
     
let is_inequality_op = function
  | OpGeq | OpGt | OpLt | OpLeq -> true
  | _ -> false

let negate_inequality_op = function
  | OpGeq -> OpLt
  | OpGt -> OpLeq
  | OpLt -> OpGeq
  | OpLeq -> OpGt
  | _ -> failwith "Can only negate inequality operators"

let string_of_binder_kind = function
  | Forall -> "forall"
  | Exists -> "exists"
  | SetComp -> failwith "string_of_binder_kind doesn't support SetComp yet!"

let string_of_pred = function
  | BtwnPred -> "Btwn"
  | ReachPred -> "Reach"
  | FramePred -> "Frame"
  | AccessPred -> "acc"
  | DisjointPred -> "Disjoint"
  | Pred (pname, _) -> pname

(** Pretty printer for SplSyntax.expr so that invariants can be printed *)
let rec string_of_expr = function
  | Null (_, _) -> "null"
  | Emp (_) -> "emp"
  | IntVal (i, _) -> Int64.to_string i
  | BoolVal (true, _) -> "true"
  | BoolVal (false, _) -> "false"
  | Read (fexp, vexp, _) -> (string_of_expr vexp) ^ "." ^ (string_of_expr fexp)
  | ProcCall ((pname, _), args_list, _) -> pname ^ "(" ^ (String.concat ", " (List.map string_of_expr args_list)) ^ ")"
  | PredApp (pred, args_list, _) -> (string_of_pred pred) ^ "(" ^ (String.concat ", " (List.map string_of_expr args_list)) ^ ")"

  | UnaryOp (OpNot, UnaryOp (OpNot, exp, _), _) -> string_of_expr exp
  | UnaryOp (OpNot, BinaryOp (exp1, OpEq, exp2, _, _), _) -> (string_of_expr exp1) ^ " != " ^ (string_of_expr exp2)
  | UnaryOp (OpNot, BinaryOp (exp1, op, exp2, t1, t2), _) when is_inequality_op op ->
     string_of_expr (BinaryOp (exp1, negate_inequality_op op, exp2, t1, t2))
  | UnaryOp (op, exp, _) -> Printf.sprintf "%s(%s)" (string_of_un_op op) (string_of_expr exp)
  | BinaryOp (exp1, OpSepStar, exp2, _, _) -> Printf.sprintf "%s %s %s" (string_of_expr exp1) (string_of_bin_op OpSepStar) (string_of_expr exp2)
  | BinaryOp (exp1, OpEq, exp2, _, _) -> Printf.sprintf "%s %s %s" (string_of_expr exp1) (string_of_bin_op OpEq) (string_of_expr exp2)
  | BinaryOp (exp1, OpOr, exp2, _, _) -> Printf.sprintf "(%s) %s (%s)" (string_of_expr exp1) (string_of_bin_op OpOr) (string_of_expr exp2)
  | BinaryOp (exp1, OpAnd, exp2, _, _) -> Printf.sprintf "(%s) %s (%s)" (string_of_expr exp1) (string_of_bin_op OpAnd) (string_of_expr exp2)
  | BinaryOp (exp1, op, exp2, _, _) -> Printf.sprintf "(%s %s %s)" (string_of_expr exp1) (string_of_bin_op op) (string_of_expr exp2)
  | Ident (id, _) -> Grass.string_of_ident id
  | Binder (SetComp, [UnguardedVar var], expr, _) -> Printf.sprintf "{%s : %s :: %s}" (fst var.v_name) (string_of_type var.v_type) (string_of_expr expr)
  | Binder (quant, vars, expr, _) -> Printf.sprintf "(%s %s :: %s)" (string_of_binder_kind quant) (String.concat ", " (List.map string_of_quant_var vars)) (string_of_expr expr)
  | New (typ, expr_list, _) ->
     Printf.sprintf "new %s(%s)" (string_of_type typ) (String.concat ", " (List.map string_of_expr expr_list))
  | Setenum (typ, expr_list, _) ->
     Printf.sprintf "Set<%s>(%s)" (string_of_type typ) (String.concat ", " (List.map string_of_expr expr_list))
  | Annot (expr, annot, _) -> Printf.sprintf "%s @(%s)" (string_of_expr expr) (string_of_annot annot)

and string_of_quant_var = function
  | GuardedVar (id, exp) -> (Grass.string_of_ident id) ^ " in " ^ (string_of_expr exp)
  | UnguardedVar var -> string_of_var_decl var

and string_of_annot = function
  | GeneratorAnnot (ematches, expr) ->
     Printf.sprintf "matching %s yields %s"
                    (String.concat ", " (List.map string_of_ematch ematches))
                    (string_of_expr expr)
  | PatternAnnot expr ->
     Printf.sprintf "pattern %s" (string_of_expr expr)
  | CommentAnnot str ->
     Printf.sprintf "comment %s" str

and string_of_ematch = function
  | (expr, []) -> string_of_expr expr
  | (expr, [(ident, _)]) -> Printf.sprintf "%s without %s" (string_of_expr expr) ident
  | _ -> failwith "ematch with several idents not yet handled."
  
let print_list chan separator printer values =
  let rec loop values =
    let v = List.hd values in
    printer chan v;
    match List.tl values with
    | [] -> ()
    | values ->
       Printf.fprintf chan "%s" separator;
       loop values in
  match values with
  | [] -> ()
  | _ -> loop values

let print_expr chan expr = Printf.fprintf chan "%s" (string_of_expr expr)

let print_var_decl chan var = Printf.fprintf chan "%s" (string_of_var_decl var)

let rec print_stmt chan indent =
  let open Printf in
  function
  | Skip _ -> fprintf chan "%sskip;\n" indent
  | Block (stmts, _) ->
     fprintf chan "%s{\n" indent;
     let newIndent = indent ^ " " in
     List.iter (print_stmt chan newIndent) stmts;
     fprintf chan "%s}\n" indent
  | LocalVars (vars, inits, _) ->
     fprintf chan "%svar " indent;
     print_list chan ", " print_var_decl vars;
     begin
       match inits with
       | None -> ();
       | Some inits ->
	  fprintf chan " := ";
	  print_list chan ", " print_expr inits;
     end;
     fprintf chan ";\n";
  | Assume (expr, pureFlag, _) ->
     fprintf chan "%s%sassume(%s);\n" indent (if pureFlag then "pure " else "") (string_of_expr expr);
  | Assert (expr, pureFlag, _) ->
     fprintf chan "%s%sassert(%s);\n" indent (if pureFlag then "pure " else "") (string_of_expr expr);
  | Assign (targetExprs, valueExprs, _) ->
     fprintf chan "%s" indent;
     if targetExprs <> [] then
       begin
	 print_list chan ", " print_expr targetExprs;
	 fprintf chan " := ";
       end;
     print_list chan ", " print_expr valueExprs;
     fprintf chan ";\n"
  | Havoc (exprs, _) ->
     fprintf chan "%shavoc " indent;
     print_list chan ", " print_expr exprs;
     fprintf chan ";\n";
  | Dispose (expr, _) ->
     fprintf chan "%sfree %s;\n" indent (string_of_expr expr);
  | If (cond, thenStmt, elseStmt, _) ->
     fprintf chan "%sif (%s)\n" indent (string_of_expr cond);
     let newIndent = indent ^ " " in
     print_stmt chan newIndent thenStmt;
     begin
       match elseStmt with
       | Skip _ -> ()
       | _ ->
	  fprintf chan "%selse\n" indent;
	  print_stmt chan newIndent elseStmt
     end;
     fprintf chan "\n";
  | Loop (contracts, _ (* Needed for scoping, ignore here *), cond, stmt, _) ->
     fprintf chan "%swhile (%s)" indent (string_of_expr cond);
     List.iter
       (function
	 | Invariant (expr, pureFlag) ->
	    fprintf chan "\n%s %sinvariant %s;" indent (if pureFlag then "pure " else "") (string_of_expr expr))
       contracts;
     fprintf chan "\n";
     print_stmt chan (indent ^ " ") stmt;
     fprintf chan "\n";
  | Return (exprs, _) ->
     fprintf chan "%sreturn " indent;
     print_list chan ", " print_expr exprs;
     fprintf chan ";\n"

let string_of_contract contract =
  let open Printf in
  match contract with
  | Requires (expr, pureFlag) ->
     sprintf "  %srequires %s;" (if pureFlag then "pure " else "") (string_of_expr expr)
  | Ensures (expr, pureFlag) ->
     sprintf "  %sensures %s;" (if pureFlag then "pure " else "") (string_of_expr expr)

let print_contracts chan =
  List.iter (fun contract -> Printf.fprintf chan "%s\n" (string_of_contract contract))
             
let print_proc_header chan proc =
  let open Printf in
  let name = fst proc.p_name in
  fprintf chan "procedure %s(" name;
  print_list chan ", " print_var_decl (List.map (fun v -> IdMap.find v proc.p_locals) proc.p_formals);
  fprintf chan ")\n";
  if proc.p_returns <> [] then
    begin
      fprintf chan "  returns (";
      print_list chan ", " print_var_decl (List.map (fun v -> IdMap.find v proc.p_locals) proc.p_returns);
      fprintf chan ")";
    end;
  print_contracts chan proc.p_contracts
                  
let print_proc_decl chan proc =
  print_proc_header chan proc;
  match proc.p_body with
  | Skip _ -> () (* Procedure without implementation *)
  | _ ->
     print_stmt chan "  " proc.p_body

let print_func_decl chan pred =
  let open Printf in
  fprintf chan "function %s(" (fst pred.pr_name);
  print_list chan ", " print_var_decl (List.map (fun v -> IdMap.find v pred.pr_locals) pred.pr_formals);
  fprintf chan ")\n";
  fprintf chan "  returns (";
  print_list chan ", " print_var_decl (List.map (fun v -> IdMap.find v pred.pr_locals) pred.pr_outputs);
  fprintf chan ")\n";
  print_contracts chan pred.pr_contracts;
  if pred.pr_body <> None then
    fprintf chan "{\n  %s\n}\n" (Util.Opt.get_or_else "" (Util.Opt.map string_of_expr pred.pr_body))

let print_pred_decl chan pred =
  if pred.pr_outputs <> [] then
    print_func_decl chan pred
  else
    let open Printf in
    fprintf chan "predicate %s(" (fst pred.pr_name);
    print_list chan ", " print_var_decl (List.map (fun v -> IdMap.find v pred.pr_locals) pred.pr_formals);
    fprintf chan ")\n";
    print_contracts chan pred.pr_contracts;  
    fprintf chan "{\n  %s\n}\n" (Util.Opt.get_or_else "" (Util.Opt.map string_of_expr pred.pr_body))

let print_typ_decl chan typ =
  let open Printf in
  match typ.t_def with
  | FreeTypeDef ->
     fprintf chan "type %s;\n" (fst typ.t_name)
  | StructTypeDef vars ->
     begin
       fprintf chan "struct %s {\n" (fst typ.t_name);
       IdMap.iter
         (fun _ field ->
           fprintf chan "  var ";
           print_var_decl chan field;
           fprintf chan ";\n")
         vars;
       fprintf chan "}\n"
     end
    
let print_decl chan decl =
  match decl with
  | VarDecl var -> print_var_decl chan var
  | ProcDecl proc -> print_proc_decl chan proc
  | PredDecl pred -> print_pred_decl chan pred
  | TypeDecl typ -> print_typ_decl chan typ

let print_spl_program chan prog =
  if prog.background_theory <> [] then failwith "Printing of background theory not supported.";
  (* These are already included in the main program at this point:
     List.iter (fun (inclFile, _) -> Printf.fprintf chan "include \"%s\"\n" inclFile) prog.includes; *)
  IdMap.iter (fun _ var -> print_var_decl chan var) prog.var_decls;
  IdMap.iter (fun _ typ -> print_typ_decl chan typ) prog.type_decls;
  IdMap.iter (fun _ pred -> print_pred_decl chan pred) prog.pred_decls;
  IdMap.iter (fun _ proc -> print_proc_decl chan proc) prog.proc_decls
  
let expr_vars expr =
  let rec loop acc = function
    | Null _
    | Emp _
    | IntVal _
    | BoolVal _ -> acc
    | Setenum (_, exprs, _)
    | New (_, exprs, _) ->
       List.fold_left
         (fun res expr -> loop res expr)
         acc exprs
    | Read (expr1, expr2, _) ->
       loop (loop acc expr2) expr1
    | ProcCall (_, exprs, _)
    | PredApp (_, exprs, _) ->
       List.fold_left
         (fun res expr -> loop res expr)
         acc exprs
    | Binder (_, quant_vars, expr, _) ->
       List.fold_left
         (fun res qvar ->
          let vname =
            match qvar with
            | GuardedVar (var, _) -> var
            | UnguardedVar var -> var.v_name in
          List.filter ((<>) vname) res)
         (loop acc expr) quant_vars
    | UnaryOp (_, expr, _) ->
       loop acc expr
    | BinaryOp (expr1, _, expr2, _, _) ->
       loop (loop acc expr2) expr1
    | Ident (var, _) -> var::acc
    | Annot (expr, _, _) -> loop acc expr in
  Util.remove_duplicates (loop [] expr)
