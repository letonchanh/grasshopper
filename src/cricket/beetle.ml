(** Check and guess shape-data invariants *)
(** Author: He Zhu *)

open Grass
open GrassUtil
open SplSyntax
open Prog
open State
open ProgInterpreter
open Util
       
(** Fixme. This is not reasonable *)
let node_typ = StructType ("LNode", 0)

(** Fixme. When curr = null I set curr.data = special_value *)
let special_value = ValInt 1000L

let badpost = ref true

(** Shape-data predicate *)
type binop =
  | Plus
  | Minus
  | Times
  | Div
  | Mod

type binrel =
  | Eq
  | Ne
  | Gt
  | Ge
  | Lt
  | Le 

type pexpr =
  | PInt of int64
  | Var of ident
  | FunApp of string * pexpr list  
  | Binop of pexpr * binop * pexpr
  | Field of string * pexpr
  | Proj of int64 * pexpr
		    
type predicateAtom =
  | True
  | Atom of pexpr * binrel * pexpr 
  | Not of predicateAtom
  | And of predicateAtom * predicateAtom
  | Or of predicateAtom * predicateAtom
  | Reach of pexpr * pexpr list * pexpr
  | Link of pexpr * pexpr list * string * pexpr * pexpr
  (*| ReachData of pexpr * pexpr list * pexpr*)
  | Forall of (ident list) * predicateAtom
  | Bool of pexpr

type invariant_atom_domain =
  (Grass.ident, SplSyntax.typ) Hashtbl.t * (predicateAtom list * predicateAtom list * predicateAtom list)

type evaluated_atoms = (predicateAtom * int) list
type evaluated_state_samples =
  (bool * evaluated_atoms * evaluated_atoms) list * (bool * evaluated_atoms) list

type learning_state =
  { observed_loop_states : (Grass.source_position, (bool * state) list) Hashtbl.t ;
    observed_pre_states  : (Grass.ident, (bool * state) list) Hashtbl.t ;
    observed_post_states : (Grass.ident, (bool * state) list) Hashtbl.t ;

    loop_invariant_atoms : (Grass.source_position, invariant_atom_domain) Hashtbl.t ;
    precondition_atoms : (Grass.ident, invariant_atom_domain) Hashtbl.t ;
    postcondition_atoms : (Grass.ident, invariant_atom_domain) Hashtbl.t ;

    observed_loop_samples : (Grass.source_position, evaluated_state_samples) Hashtbl.t ;
    observed_pre_samples : (Grass.ident, evaluated_state_samples) Hashtbl.t ;
    observed_post_samples : (Grass.ident, evaluated_state_samples) Hashtbl.t ;

    inferred_loop_invariants : (Grass.source_position, ((Grass.ident * Grass.ident) * SplSyntax.expr) list) Hashtbl.t ;
    inferred_preconditions : (Grass.ident, ((Grass.ident * Grass.ident) * SplSyntax.expr) list) Hashtbl.t ;
    inferred_postconditions : (Grass.ident, ((Grass.ident * Grass.ident) * SplSyntax.expr) list) Hashtbl.t ;

    mutable generated_predicates : decl list;
  }

let pprint_op = function
  | Plus -> "+"
  | Minus -> "-"
  | Times -> "*"
  | Div -> "/"
  | Mod -> "%"

let pprint_rel = function
    Eq -> "="
  | Ne -> "!="
  | Gt -> ">"
  | Ge -> ">="
  | Lt -> "<"
  | Le -> "<="

let rel_to_func = function
  | Eq -> (=)
  | Ne -> (<>)
  | rel ->
     (fun v1 v2 ->
      let getValue = function
        | ValInt v -> v
        | ValAddr 0L -> 0L
        | _ -> failwith "Trying to relate address values with >/>=/<=/<." in
      let (x, y) = (getValue v1, getValue v2) in
      match rel with
      | Gt -> Int64.compare x y > 0
      | Ge -> Int64.compare x y >= 0
      | Lt -> Int64.compare x y < 0
      | Le -> Int64.compare x y <= 0
      | _ -> failwith "Forgot a relation."
     )

let rel_negation = function
  | Eq -> Ne
  | Ne -> Eq
  | Gt -> Le
  | Ge -> Lt
  | Lt -> Ge
  | Le -> Gt
	    
let (||.) p q = Or (p, q)

let (&&.) p q = And (p, q)        

let implies(p, q) = Or ((Not p), q)
		       
let big_or = function
  | c :: cs -> List.fold_left (||.) c cs
  | [] -> Not True        

let big_and = function
  | c :: cs -> List.fold_left (&&.) c cs
  | [] -> True

let virpos = { sp_file = "";
               sp_start_line = (-1);
               sp_start_col = (-1);
               sp_end_line = (-1);
               sp_end_col = (-1);
             }
let forall_uvar = fresh_ident "uu"
let forall_vvar = fresh_ident "vv"
let forall_uexpr = Var forall_uvar
let forall_vexpr = Var forall_vvar
let null_var = fresh_ident "null"
let null_expr = Var null_var

(** Util functions *)
let rec lflap es =
  match es with
  | s :: [] ->
     List.map (fun c -> [c]) s
  | s :: es ->
     flat_map (fun c -> List.map (fun d -> c :: d) (lflap es)) s
  | [] ->
     []            
       
let rec find_map f xs =
  match xs with
  | [] -> raise Not_found
  | x::xs -> 
     (match f x with
      | None -> find_map f xs
      | Some res -> res)
       
let rec print_list pr sep ppf =
  function
    [] -> ()
  | [a] -> pr ppf a
  | a :: l -> pr ppf a; sep ppf; print_list pr sep ppf l

let pprint_list sepstr pp =
  (fun ppf -> print_list pp
			 (fun ppf -> Format.fprintf ppf "%s@;<1 2>" sepstr) ppf)

let print_var var =
  fst var
(*string_of_ident var*)

let str_contains s1 s2 =
  let re = Str.regexp_string s2 in
  try 
    ignore (Str.search_forward re s1 0); 
    true
  with Not_found -> false
		      
let exp_var expr = match expr with
  | Var var -> var
  | _ -> assert false

let rec pprint_pexpr ppf = function
  | PInt n ->
     if Int64.compare n 0L < 0 then Format.fprintf ppf "(0 - %Ld)" (Int64.neg n)
     else Format.fprintf ppf "%Ld" n
  | Var x ->
     Format.fprintf ppf "%s" ((print_var) x)
  | FunApp (f, pexp) ->
     Format.fprintf ppf "@[(%s@ %a)@]" f (pprint_list " " pprint_pexpr) pexp
  | Binop (p, op, q) ->
     let opstr = match op with
       | Plus -> "+"
       | Minus -> "-"
       | Times -> "*"
       | Div -> "/"
       | Mod -> "%"
     in Format.fprintf ppf "@[(%a@ %s@ %a)@]" pprint_pexpr p opstr pprint_pexpr q
  | Field (f, pexp) ->
     Format.fprintf ppf "@[%a.%s@]" pprint_pexpr pexp f
  | Proj (n, pexp) ->
     Format.fprintf ppf "@[%a.%Ld@]" pprint_pexpr pexp n

let rec pprint ppf = function
  | True ->
     Format.fprintf ppf "true"
  | Atom (p, rel, q) ->
     Format.fprintf ppf "@[(%a@ %s@ %a)@]" pprint_pexpr p (pprint_rel rel) pprint_pexpr q
  | Not (Atom (p, rel, q)) ->
     pprint ppf (Atom (p, rel_negation rel, q))
  | Or (Not p, q) ->
     Format.fprintf ppf "@[(%a) ==>@, %a@]" pprint p pprint q
  | Not p ->
     Format.fprintf ppf "@[(-.@ %a)@]" pprint p
  | And (p, q) ->
     Format.fprintf ppf "@[(%a@ && %a)@]" flatten_conjuncts p flatten_conjuncts q
  | Or (p, q) ->
     Format.fprintf ppf "@[(%a@ || %a)@]" flatten_disjuncts p flatten_disjuncts q
  | Reach (d, endpoints, u) -> 
     Format.fprintf ppf "@[(%s@ (%a, %a, %a))@]" "reach" pprint_pexpr d (pprint_list " " pprint_pexpr) endpoints pprint_pexpr u
  | Link (d, endpoints, f, u, v)    ->
     Format.fprintf ppf "@[%s@ (%a, %a, %s, %a, %a)@]" 
		    "link" pprint_pexpr d (pprint_list " " pprint_pexpr) endpoints f pprint_pexpr u pprint_pexpr v    
  (*| ReachData (d, endpoints, u) ->
            Format.fprintf ppf "@[(%s@ (%a, %a, %a))@]" "reach" pprint_pexpr d (pprint_list " " pprint_pexpr) endpoints pprint_pexpr u*)
  | Forall ([], p) ->
     pprint ppf p
  | Forall (ps, p) ->
     Format.fprintf ppf "@[forall (%s).@, %a@]"
		    (String.concat ", " (List.map print_var ps)) pprint p 
  | Bool b -> Format.fprintf ppf "@[%a@]" pprint_pexpr b
and flatten_conjuncts ppf = function
  | And (And (p1, p2), And (q1, q2)) ->
     Format.fprintf ppf "@[%a@;<1 0>%a@;<1 0>%a@;<1 0>%a@]"
		    flatten_conjuncts p1 flatten_conjuncts p2
		    flatten_conjuncts q1 flatten_conjuncts q2
  | And (And (p1, p2), q)
  | And (q, And (p1, p2)) ->
     Format.fprintf ppf "@[%a@;<1 0>%a@;<1 0>%a@]"
		    pprint q flatten_conjuncts p1 flatten_conjuncts p2
  | p -> pprint ppf p
and flatten_disjuncts ppf = function
  | Or (Or (p1, p2), Or (q1, q2)) ->
     Format.fprintf ppf "@[%a@ ||@;<1 0>%a@ ||@;<1 0>%a@ ||@;<1 0>%a@]"
		    flatten_disjuncts p1 flatten_disjuncts p2
		    flatten_disjuncts q1 flatten_disjuncts q2
  | Or (Or (p1, p2), q)
  | Or (q, Or (p1, p2)) ->
     Format.fprintf ppf "@[%a@ ||@;<1 0>%a@ ||@;<1 0>%a@]"
		    pprint q flatten_disjuncts p1 flatten_disjuncts p2
  | p -> pprint ppf p

let string_of_cond c = pprint Format.str_formatter c; Format.flush_str_formatter ()

(** Collect variables in predicate *)
let exp_vars_unexp = function
  | PInt _ -> ([], [])
  | Var x -> ([], [x])
  | Binop (e1, _, e2) -> ([e1; e2], [])
  | FunApp (_, es) -> (es, [])
  | Field (_, e) | Proj (_, e) -> ([e], [])

let exp_vars e =
  expand exp_vars_unexp [e] []

let var_unexp = function
  | True -> ([], [])
  | Atom (e1, _, e2) -> ([], exp_vars e1 @ exp_vars e2)
  | Not p -> ([p], [])
  | And (p, q) | Or (p, q) -> ([p; q], [])
  | Reach (d, endpoints, u) -> ([], exp_vars d @ exp_vars u @ List.fold_left (fun res endpoint -> res @ (exp_vars endpoint)) [] endpoints)
  | Link (d, endpoints, f, u, v)    -> ([], exp_vars d @ exp_vars u @ exp_vars v @ List.fold_left (fun res endpoint -> res @ (exp_vars endpoint)) [] endpoints)
  (*| ReachData (d, endpoints, u) -> ([], exp_vars d @ exp_vars u @ List.fold_left (fun res endpoint -> res @ (exp_vars endpoint)) [] endpoints) *)
  | Forall (_, p) -> ([p], [])
  | Bool b -> ([], exp_vars b)

let var_quantifier_exp = function
  | True -> ([], [])
  | Atom (e1, _, e2) -> ([], [])
  | Not p -> ([p], [])
  | And (p, q) | Or (p, q) -> ([p; q], [])
  | Reach (d, endpoints, u) -> ([], [])
  | Link (d, endpoints, f, u, v)    -> ([], [])
  | Forall (ps, p) -> ([p], ps)
  | Bool b -> ([], [])

let quantifiers e = 
  expand var_quantifier_exp [e] []

(* vars function does not return universall quantified variables *)
let vars e =
  let vars = expand var_unexp [e] [] in
  let quantifiers = expand var_quantifier_exp [e] [] in
  List.filter (fun var -> 
               List.for_all (fun quantifier -> not (var = quantifier)) quantifiers) vars 
              
let rec pexp_map_vars f pexp =
  let rec map_rec = function
      Var x -> f x
    | FunApp (fn, e) ->
       FunApp (fn, List.map map_rec e)
    | Binop (e1, op, e2) ->
       Binop (map_rec e1, op, map_rec e2)
    | Field (f, pexp) ->
       Field (f, map_rec pexp)
    | Proj (n, pexp) ->
       Proj (n, map_rec pexp)
    | e ->
       e
  in map_rec pexp

let rec map_vars f pred =
  let rec map_rec = function
      True ->
      True
    | Atom (e1, rel, e2) ->
       Atom (pexp_map_vars f e1, rel, pexp_map_vars f e2)
    | Not p ->
       Not (map_rec p)
    | And (p, q) ->
       And (map_rec p, map_rec q)
    | Or (p, q) ->
       Or (map_rec p, map_rec q)
    | Reach (d, endpoints, u) ->
       Reach (pexp_map_vars f d, List.map (fun e ->  pexp_map_vars f e) endpoints, pexp_map_vars f u)
    | Link (d, endpoints, field, u, v)    ->
       Link (pexp_map_vars f d, List.map (fun e -> pexp_map_vars f e) endpoints, field, pexp_map_vars f u, pexp_map_vars f v)
    (*| ReachData (d, endpoints, u) ->
                Reach (pexp_map_vars f d, List.map (fun e ->  pexp_map_vars f e) endpoints, pexp_map_vars f u) *)
    | Forall (ps, p) -> 
       Forall (ps, map_rec p)
    | Bool b -> Bool (pexp_map_vars f b)
  in map_rec pred        
             
let subst v x pred = map_vars (fun y -> if x = y then v else Var y) pred    

let rec andlist p = match p with
  | And (p1, p2) -> (andlist p1) @ (andlist p2)  
  | _ -> [p] 

let rec orlist p = match p with
  | Or (p1, p2) -> (orlist p1) @ (orlist p2)  
  | _ -> [p] 

(** Encdoe grass predicates to learning predicates *)
let encode splexp = 
  match splexp with
  | Ident (ident, _) -> Var ident
  | Null _ -> null_expr
  | _ -> assert false

(** decdoe learning predicates to grass predicates *)
let convertRel op = 
  match op with
  | Eq -> OpEq
  | Ne -> assert false
  | Gt -> OpGt
  | Ge -> OpGeq
  | Lt -> OpLt
  | Le -> OpLeq 

let dummy_pos = GrassUtil.dummy_position

let getFootprintId x y = ("FP__" ^ (fst x) ^ "__" ^ (fst y), 0)
            
let nextCandidateInvId = ref 0 
let decode varToType invariants =  
  let rec convertExp exp = 
    match exp with
    | PInt n -> 
       IntVal (n, dummy_pos)
    | Var x ->
       if (x = null_var) then Null (node_typ, dummy_pos)
       else Ident (x, dummy_pos)
    | FunApp (f, pexp) -> assert false
    | Binop (p, opr, q) ->
       let opr = match opr with
         | Plus -> OpPlus
         | Minus -> OpMinus
         | Times -> OpMult
	 | Div -> OpDiv
	 | Mod -> assert false
       in BinaryOp (convertExp p, opr, convertExp q, IntType, dummy_pos)
    | Field (f, pexp) ->
       Read (Ident ((f, 0), dummy_pos), convertExp pexp, dummy_pos)
    | Proj (n, pexp) ->
       Read (Ident ((Int64.to_string n, 0), dummy_pos), convertExp pexp, dummy_pos) in

  let getFootprintIdFromExprs x y =
    match (x, y) with
    | (Ident (xId, _), Ident (yId, _)) -> getFootprintId xId yId
    | (Ident (xId, _), Null _) -> getFootprintId xId ("null", 0)
    | _ -> assert false
  in
  
  let rec convert inv =
    match inv with
    | True -> assert false
    | Bool b -> assert false
    | Atom (p, Ne, q) -> UnaryOp (OpNot, BinaryOp (convertExp p, OpEq, convertExp q, BoolType, dummy_pos), dummy_pos)
    | Atom (p, rel, q) ->
       BinaryOp (convertExp p, convertRel rel, convertExp q, BoolType, dummy_pos)
    | Not p ->
       UnaryOp (OpNot, convert p, dummy_pos)
    | Forall (ps, Or (Not (Reach (listStart, listEndpoints, quantVarU)), predicate)) ->
       let listStartExpr = convertExp listStart in
       let listEndExpr = convertExp (List.hd listEndpoints) in
       let quantVarUExpr = convertExp quantVarU in
       let footprintIdent = Ident (getFootprintIdFromExprs listStartExpr listEndExpr, dummy_pos) in
       let ps = List.map (fun q ->
			  UnguardedVar { v_name = q;
					 v_type = node_typ; 
					 v_ghost = false;
					 v_implicit = false;
					 v_aux = false;
					 v_pos = dummy_pos;
					 v_scope = dummy_pos;
                                       }) ps in
       let constr =
         BinaryOp
           (BinaryOp
              (quantVarUExpr, OpIn, footprintIdent, BoolType, dummy_pos), 
	    OpImpl, convert predicate, BoolType, dummy_pos) in
       Binder (SplSyntax.Forall, ps, constr, dummy_pos)
    | Forall (ps, Or (Not (Link (listStart, listEndpoints, listField, quantVarU, quantVarV)), predicate))    ->
       let listStartExpr = convertExp listStart in
       let listEndExpr = convertExp (List.hd listEndpoints) in
       let quantVarUExpr = convertExp quantVarU in
       let quantVarVExpr = convertExp quantVarV in       
       let footprintIdent = Ident(getFootprintIdFromExprs listStartExpr listEndExpr, dummy_pos) in
       let ps = List.map (fun q ->
			  UnguardedVar { v_name = q;
					 v_type = node_typ; 
					 v_ghost = false;
					 v_implicit = false;
					 v_aux = false;
					 v_pos = dummy_pos;
					 v_scope = dummy_pos;
                                       }) ps in
       let reachconstru = BinaryOp (quantVarUExpr, OpIn, footprintIdent, BoolType, dummy_pos) in
       let reachconstrv = BinaryOp (quantVarVExpr, OpIn, footprintIdent, BoolType, dummy_pos) in
       let btwn = PredApp (BtwnPred, [Ident ((listField, 0), dummy_pos); listStartExpr; quantVarUExpr;  quantVarVExpr], dummy_pos) in 
       let left = BinaryOp (reachconstru, OpAnd, reachconstrv, BoolType, dummy_pos) in
       let left =  BinaryOp (left, OpAnd, btwn, BoolType, dummy_pos) in
       let right = convert predicate in
       Binder (SplSyntax.Forall, ps, BinaryOp (left, OpImpl, right, BoolType, dummy_pos), dummy_pos)
    | Or (p, q) ->
       BinaryOp (convert p, OpOr, convert q, BoolType, dummy_pos)    
    | And (p, q) ->
       BinaryOp (convert p, OpAnd, convert q, BoolType, dummy_pos)
    | Forall (ps, p) -> (assert (ps = []); convert p)
    | _ -> assert false in
  
  (** Fixme. Not general *)                
  let searchFP inv = 
    let rec loop inv = 
      match inv with
      | True -> []
      | Bool b -> []
      | Atom _ -> []
      | Not p -> loop p
      | Or (p, q) -> loop p @ loop q
      | And (p, q) -> loop p @ loop q
      | Forall (_, p) -> loop p
      | Link (d, endpoints, _, _, _) -> [(exp_var d, exp_var (List.hd endpoints))]
      | Reach (d, endpoints, _) -> [(exp_var d, exp_var (List.hd endpoints))] 
    (*| ReachData _ -> assert false*) in
    let res = loop inv in
    let _ = assert (List.length res = 1) in
    let res = List.hd res in
    (fst res, snd res) in
  
  
  let invtbl = Hashtbl.create 5 in
  let _ =
    List.iter
      (fun inv -> 
	let s, t = 
	  try searchFP inv
	  with _ -> (null_var, null_var) in
	if (Hashtbl.mem invtbl (s, t)) then
	  Hashtbl.replace invtbl (s, t) (inv::(Hashtbl.find invtbl (s, t)))
	else
	  Hashtbl.add invtbl (s, t) [inv]
      ) invariants in
  
  Hashtbl.fold
    (fun (s, t) invs res -> 
      ( (* Inserting candidate invariants *)
	let inv = big_and invs in

        (***** Make a predicate declaration for the discovered invariant *)

        (*** Step 1: Identify needed program variables that need to be passed in: *)
        let needs_footprint = s <> null_var || t <> null_var in
        let inv_vars = remove_duplicates (vars inv) in
	let inv_vars = List.filter (fun v -> v <> s && v <> t) inv_vars in
        (* Add footprint, if needed. *)
        let pred_formals = [] in (* if needs_footprint then [getFootprintId s t] else [] in *)
        let pred_formals = inv_vars @ pred_formals in 
        let pred_formals = if (s = t) then s::pred_formals else s::t::pred_formals in
	let pred_formals = List.filter ((<>) null_var) pred_formals in

        (*** Step 2: Declare types for the variables: *)
        let pred_locals =
          List.fold_left (
	      fun res varId ->
	        IdMap.add
                  varId
		  { v_name = varId;
		    v_type =
                      if varId = getFootprintId s t then
                        SetType node_typ
                      else
                        if (Hashtbl.mem varToType varId) then
			  match Hashtbl.find varToType varId with
			  | StructType _ -> node_typ
			  | IdentType _ -> node_typ
			  | IntType -> IntType
			  | _ -> assert false
		        else node_typ;
		    v_ghost = false;
		    v_implicit = false;
		    v_aux = false;
		    v_pos = dummy_pos;
		    v_scope = dummy_pos;
		  } res
	  ) IdMap.empty pred_formals in

        (*** Step 3: Build actual predicate: *)
       (** Fixme. No general *)
        let pred_body = convert inv in
        let pred_body =
          if needs_footprint then
            let footprintId = getFootprintId s t in
            let footprintIdent = Ident(footprintId, dummy_pos) in
            let listPred = PredApp (Pred ("lseg", 0), [convertExp (Var s); convertExp (Var t)], dummy_pos) in
            let accPred = ProcCall (("acc", 0), [footprintIdent], dummy_pos) in
            let footprintDecl =
              { v_name = footprintId;
                v_type = SetType node_typ;
                v_ghost = false;
                v_implicit = false;
                v_aux = false;
                v_pos = dummy_pos;
                v_scope = dummy_pos;
              } in
            let constr = BinaryOp(BinaryOp(listPred, OpAnd, accPred, BoolType, dummy_pos), OpSepStar, pred_body, BoolType, dummy_pos) in
            Binder (Exists, [UnguardedVar footprintDecl], constr, dummy_pos)
          else
            pred_body in
        let pred_name = fresh_ident ("Candidate" ^ (string_of_int !nextCandidateInvId)) in
        let pred =
          { pr_name = pred_name;
            pr_formals = pred_formals;
            pr_outputs = [];
            pr_locals = pred_locals;
            pr_contracts = [];
            pr_body = Some pred_body;
            pr_pos = dummy_pos;
          } in
        
        (* Return the declaration and call to the declaration *)
        let pred_actuals =
          List.map
            (fun formalPar -> 
	      if (formalPar = null_var) then Null (node_typ, dummy_pos) 
	      else Ident (formalPar, dummy_pos))
            pred_formals in

        let invariantCall = PredApp (Pred pred_name, pred_actuals, dummy_pos) in
        
        let _ = incr nextCandidateInvId in
        ((s, t), PredDecl pred, invariantCall)
      ) :: res
    ) invtbl []         

(** Extract the shape specification of the program *)
let extract_shape_predicates spl_prog proc_name = 
  let proc = try
      Grass.IdMap.find proc_name spl_prog.proc_decls
    with
      Not_found -> failwith ("Couldn't find the procedure " ^ (fst proc_name))
  in
  let loop_specs = Hashtbl.create 5 in
  let rec find_inv_from_stmt = function
    | Block (stmt_list, pos) ->
       List.iter find_inv_from_stmt stmt_list
    | If (e, stmt1, stmt2, pos) -> 
       (find_inv_from_stmt stmt1;
	find_inv_from_stmt stmt2)
    | Loop (contracts, stmt1, e, stmt2, pos) ->
       (** invariants in the contract are this loop's shape specification *)
       let specs =
	 List.fold_left
	   (fun res (Invariant (inv, b)) -> 
	    if b then res
	    else res @ [inv])
	   [] contracts in
       (find_inv_from_stmt stmt1;
	find_inv_from_stmt stmt2;
	Hashtbl.replace loop_specs pos specs)
    | s -> () in
  find_inv_from_stmt proc.p_body;
  
  (* Deal with pre/post-conditions *)
  let (pre_specs, post_specs) =
    List.fold_left
      (fun (pre, post) contract ->
	match contract with
	| Requires (inv, false) -> (inv::pre, post)
	| Ensures (inv, false) -> (pre, inv::post)
	| _ -> (pre, post)
      ) ([], []) proc.p_contracts in 
  (loop_specs, pre_specs, post_specs)

(** Replace pure shape loop invariant with shape-data loop invariant. *)
let insert_invariants spl_prog loopPos shapeDataPredicates =
  let (procName, proc) = Cricket.find_proc_by_pos spl_prog loopPos in

  let rec insert_inv_in_stmt = function
    | Block (stmt_list, pos) -> Block (insert_inv_in_stmt_list stmt_list, pos)
    | If (e, stmt1, stmt2, pos) -> If (e, insert_inv_in_stmt stmt1,
				       insert_inv_in_stmt stmt2, pos)
    | Loop (shapeInvariants, stmt1, e, stmt2, pos) ->
       if pos = loopPos then
	 let rec add_data_to_inv = function
           | ProcCall (("lseg", _), listStart :: listEnd, _)
           | PredApp (Pred ("lseg", _), listStart :: listEnd, _) as shapePredicate ->
              begin
                let (listStart, listEnd) = (exp_var (encode listStart), exp_var (encode (List.hd listEnd))) in
                try
                  List.assoc (listStart, listEnd) shapeDataPredicates
                with Not_found -> shapePredicate
              end
           | UnaryOp (whatever, exp, whatever2) -> UnaryOp (whatever, add_data_to_inv exp, whatever2)
           | BinaryOp (exp1, whatever, exp2, whatever2, whatever3) ->
              BinaryOp (add_data_to_inv exp1, whatever, add_data_to_inv exp2, whatever2, whatever3)
           | whatever -> whatever 
	 in
	 let shapeDataInvariants =
           List.map
	     (fun invariant ->
              match invariant with
              | Invariant (inv, true) -> invariant
	      | Invariant (inv, false) -> Invariant (add_data_to_inv inv, false))
	     shapeInvariants in
         (* Maybe insert data invariant unrelated to any shape predicate. *)
	 let shapeDataInvariants =
           try
             let pureDataInvariant = List.assoc (null_var, null_var) shapeDataPredicates in
             shapeDataInvariants @ [(Invariant (pureDataInvariant, false))]
           with Not_found -> shapeDataInvariants in
	 Loop (shapeDataInvariants, insert_inv_in_stmt stmt1, e, insert_inv_in_stmt stmt2, pos)
       else Loop (shapeInvariants, insert_inv_in_stmt stmt1, e, insert_inv_in_stmt stmt2, pos)
    | s -> s
  and insert_inv_in_stmt_list = function
    | st :: stmt_list ->
       (insert_inv_in_stmt st) :: (insert_inv_in_stmt_list stmt_list)
    | [] -> [] 
  in
  let proc = {proc with p_body = insert_inv_in_stmt proc.p_body} in
  {spl_prog with proc_decls = Grass.IdMap.add procName proc spl_prog.proc_decls}

let insert_pre_post_conditions spl_prog proc_name prespecs postspecs =
  let proc = IdMap.find proc_name spl_prog.proc_decls in
  let contracts = proc.p_contracts in
  
  let rec add_lseg_data_inv pre = function
    | ProcCall (("lseg", _), head :: rest, _)
    | PredApp (Pred ("lseg", _), head :: rest, _) as whatever ->
       let head, tl = exp_var (encode head), exp_var (encode (List.hd rest)) in
       let invs = if pre then prespecs else postspecs in
       if List.mem_assoc (head, tl) invs then
	 List.assoc (head, tl) invs
       else whatever
    | UnaryOp (whatever, exp, whatever2) -> UnaryOp (whatever, add_lseg_data_inv pre exp, whatever2)
    | BinaryOp (exp1, whatever, exp2, whatever2, whatever3) ->
       BinaryOp (add_lseg_data_inv pre exp1, whatever, add_lseg_data_inv pre exp2, whatever2, whatever3)
    | whatever -> whatever in
  
  let contracts =
    List.map
      (fun contract -> 
        match contract with
	| Requires (spec, false) -> Requires (add_lseg_data_inv true spec, false)
	| Ensures (spec, false) -> 
	   let ensure = add_lseg_data_inv false spec in
	   Ensures (ensure, false)
	| _ -> contract
      ) contracts in
  
  let contracts = 
    if (List.mem_assoc (null_var, null_var) postspecs) then
      let inv = List.assoc (null_var, null_var) postspecs in
      contracts @ [(Ensures (inv, false))]
    else contracts in
  
  let proc = {proc with p_contracts = contracts} in
  {spl_prog with proc_decls = Grass.IdMap.add proc_name proc spl_prog.proc_decls}

(** Find all lseg(x, y) in a shape invariants. TODO: Lift to other predicate types *)
let find_lsegs shape_invariant =
  let rec add_lsegs lsegs = function
    | ProcCall (("lseg", _), head :: target :: [], _)
    | PredApp (Pred ("lseg", _), head :: target :: [], _) ->
       (head, target) :: lsegs
    | UnaryOp (_, exp, _) -> add_lsegs lsegs exp
    | BinaryOp (exp1, _, exp2, _, _) ->
       add_lsegs (add_lsegs lsegs exp1) exp2
    | _ -> lsegs
  in
  List.fold_left add_lsegs [] shape_invariant

(** typing atomic predicates *)
let kind_of pred = (* TODO: This should be a proper type. *)
  (* Link _ -> 2; reach (_, u) or reach (_, v) -> 1; pred(u) or pred(v) -> 0; curr = null -> (-1); otherwise -> (-2) *)
  match pred with
  | Link _ -> 2
  | Reach (_, _, u) when (u = forall_uexpr || u = forall_vexpr) -> 1
  | pred ->
     let predVars = vars pred in
     if List.exists (fun var -> var = forall_uvar || var = forall_vvar) predVars then
       0
     else if List.mem null_var predVars then
       -1
     else
       (match pred with
	| Atom (_, Eq, _) (* curr == y *) -> (-2)
	| Atom (Field _, _, Field _) (* curr.data <= y.data*) -> (-4)
	| Atom (Field _, _, _)
	| Atom (_, _, Field _) (* curr.data <= ub*) -> (-3)
	| _ -> assert false
       )

(** General predicate domain for shape-data invariants 
 *  Strategy: use the extracted shape predicates and generate atomic predicates from 
 *    the definitions of the shape predicates
 *)
type predicateUse = Precondition | Postcondition | LoopInvariant
let generate_atomic_predicates predUse proc pos shape_invariant =
  let lsegs = find_lsegs shape_invariant in
  Cricket.log_verbose
    ("Generating atomic reachability predicates for the following lists: "
     ^ (String.concat " " (List.map (fun (x, y) -> ((SplSyntax.string_of_expr x) ^ "->" ^ (SplSyntax.string_of_expr y))) lsegs)));

  (* Use a dictionary to cache all the variables used *)
  let varnameToType = Hashtbl.create 7 in

  (* TODO: These hardcoded things should be more dynamic (extract from def. of shape predicate?) *)
  let next_fld = "next" in
  let data_fld = "data" in

  (* Extract variable names occurring in the considered list segments *)
  let structVars =
    List.fold_left
      (fun res (x, y) ->
       let res =
	 match x with
	 | Ident (ident, _) -> ident::res
	 | Null _ -> res
	 | _ -> assert false in
       match y with
       | Ident (ident, _) -> ident::res
       | Null _ -> res
       | _ -> assert false) [] lsegs in

  let varInScope var =
    let varpos = var.v_scope in
    varpos.Grass.sp_start_line <= pos.Grass.sp_start_line &&
      varpos.Grass.sp_end_line >= pos.Grass.sp_end_line in

  let storeTypedVariable varnameToType (intVars, structVars) varName varType =
    Hashtbl.replace varnameToType varName varType;
    match varType with
    | IntType -> (intVars @ [varName], structVars)
    | StructType _ -> (intVars, structVars @ [varName])
    | IdentType _ -> (intVars, structVars @ [varName])       
    | _ -> (intVars, structVars) in
    
  (* Also extract variables occurring in the program. *)
  let (intVars, structVars) =
    Grass.IdMap.fold
      (fun _ var (intVars, structVars) -> 
       (* We do not need want to consider return variable which are believed to only appear in specifications *)
       let (varName, varType) = (var.v_name, var.v_type) in
       match predUse with
       | Precondition when List.mem varName proc.p_formals -> (* Only use formal parameters for pre. *)
          storeTypedVariable varnameToType (intVars, structVars) varName varType
       | LoopInvariant when not(List.mem varName proc.p_returns) -> (* Use everything but returns. *)
          storeTypedVariable varnameToType (intVars, structVars) varName varType
       | Postcondition when varInScope var ->
          storeTypedVariable varnameToType (intVars, structVars) varName varType
       | _ ->
	  (intVars, structVars))
      (proc.p_locals) ([], structVars) in
  let structVars = remove_duplicates structVars in
  (** Only in local structVars (that are not parameters / returns) *)
  let structVars' =
    List.filter (fun stvar -> List.for_all (fun formal -> formal <> stvar) proc.p_formals) structVars in
  (** Pairs over all struct variables *)
  let structVarPairs = pairs structVars in

  (***** Enumerate the actual predicates. Follows top-down order of kind_of from above. *)
  (* Kind 2/1: Shape atoms (expression reachability of variables) *)
  let shapePredicates =
    List.fold_left
      (fun res (x, y) ->
       res @ [Link (encode x, [encode y], next_fld, forall_uexpr, forall_vexpr); (* (x -next-> y, uu, vv) *)
	      Reach (encode x, [encode y], forall_uexpr)]) (* (x ->+ y, uu) *)
      [] lsegs in

  (* Kind 0: Data comparisons on quantified variables. *)
  (** \forall uu, vv . uu.data <= vv.data / vv.data <= uu.data *)
  let dataDataCmpPreds =
    [ Atom (Field(data_fld, forall_uexpr), Le, Field (data_fld, forall_vexpr))
    ; Atom (Field(data_fld, forall_vexpr), Le, Field (data_fld, forall_uexpr))] in

  (** \forall uu . uu.data <= structVar.data / structVar.data <= uu.data *)
  let dataStructLocalCmpPreds =
    Util.flat_map
      (fun structVar ->
       [Atom (Field (data_fld, forall_uexpr), Le, Field (data_fld, Var structVar));
	Atom (Field (data_fld, Var structVar), Le, Field (data_fld, forall_uexpr))]) structVars' in

  (** \forall uu . uu.data <= intVar / intVar <= uu.data *)
  let dataIntLocalCmpPreds =
    Util.flat_map
      (fun intVar ->
       [Atom (Field (data_fld, forall_uexpr), Le, Var intVar);
	Atom (Var intVar, Le, Field (data_fld, forall_uexpr))]) intVars in

  (** Kind -1: Equality with null pointer. *)
  let structLocalNullCmpPreds =
    List.map (fun structVar -> Atom (Var structVar, Eq, null_expr)) structVars' in

  (** Kind -2: Equalities between local variables. *)
  let structLocalStructLocalEqPreds =
    List.map (fun (structVar1, structVar2) -> Atom (Var structVar1, Eq, Var structVar2)) structVarPairs in

  (** Kind -3: structVar.data <= intVar / intVar <= structVar.data [Restricted to those struct variables that aren't formal parameters]*)
  let structLocalIntLocalCmpPreds =
    Util.flat_map
      (fun structVar ->
       Util.flat_map
	 (fun intVar ->
	  [ Atom (Var intVar, Le, Field (data_fld, Var structVar))
	  ; Atom (Field (data_fld, Var structVar), Le, Var intVar)]) intVars
      ) structVars' in

  (** Kind -4: structVar1.data <= structVar2.data / structVar1.data <= structVar2.data *)
  let structLocalStructLocalDataCmpPreds =
    Util.flat_map
      (fun (structVar1, structVar2) ->
       [ Atom (Field (data_fld, Var structVar1), Le, Field (data_fld, Var structVar2))
       ; Atom (Field (data_fld, Var structVar2), Le, Field (data_fld, Var structVar1))]) structVarPairs in

  let dataPredicates =
      dataDataCmpPreds
    @ dataIntLocalCmpPreds
    @ dataStructLocalCmpPreds
    @ structLocalNullCmpPreds
    @ structLocalIntLocalCmpPreds
    @ structLocalStructLocalEqPreds in
  (varnameToType, (shapePredicates, dataPredicates, structLocalStructLocalDataCmpPreds))

module Int : Graph.Sig.COMPARABLE with type t = Int64.t =
						  struct
						    type t = int64
						    let compare = Int64.compare
						    let hash = Hashtbl.hash
						    let equal = (=)
						  end
module G = Graph.Imperative.Digraph.Concrete(Int)
module PC = Graph.Path.Check(G)
module DotGraph =
  struct
    type t = G.t
    module V = G.V
    module E = G.E
    let iter_vertex = G.iter_vertex
    let iter_edges_e = G.iter_edges_e
    let graph_attributes g = []
    let default_vertex_attributes g = [`Shape `Box]
    let vertex_name i = Printf.sprintf "V_%Ld" i 
    let vertex_attributes v = [`Label (vertex_name v)]
    let default_edge_attributes g = []
    let edge_attributes e = []
    let get_subgraph v = None
  end
module Dot = Graph.Graphviz.Dot(DotGraph) 
let dump_graph g = 
  (Dot.fprint_graph Format.std_formatter g;
   Format.fprintf Format.std_formatter "@.")

let heapgraph_from_state links =
  let g = G.create () in
  let nodes =
    Hashtbl.fold
      (fun (addr, fname) value res ->
       match value with
       | ValInt _ -> res
       | ValAddr a ->
       (* TODO: This hardcodes that we ignore self-cycles. This should actually be structure-dependent. *)
       if addr = a then
	 res
       else
	 (G.add_edge g addr a;
	  if (a = 0L) then
	    addr::res
	  else
	    addr::(a::res)))
      links [] in
  (remove_duplicates nodes, g)
    
let rec evaluate_expr scalars (heap : ((int64 * string), valu) Hashtbl.t) exp =
  let get_field f = 
    List.hd (Str.split (Str.regexp "_") f) in
  let get_version f =
    let res = Str.split (Str.regexp "_") f in
    if List.length res <= 1 then 0
    else int_of_string (List.nth res 1) in
  let get_latest (heap : ((int64 * string), valu) Hashtbl.t) v f =
    let entries = Hashtbl.fold (fun (v', f') _ res -> 
				let f'' = get_field f' in
				if v = v' && f = f'' then (v', f')::res
				else res 
			       ) heap [] in
    if (entries = []) then special_value
    else
      let latest = List.fold_left (fun (resv, resf) (v, f) -> 
				   let resversion = get_version resf in
				   let fversion = get_version f in
				   if fversion > resversion then (v, f)
				   else (resv, resf)
				  ) (List.hd entries) (List.tl entries) in
      Hashtbl.find heap latest in
  match exp with
  | Var v ->
     begin
       let varname = print_var v in
       if varname = "nondet" then assert false
       else if varname = "null" then ValAddr 0L
       else
	 try
	   List.assoc varname scalars
	 with
	   Not_found -> ValAddr 0L
	   (* TODO: This shouldn't happen at all...
              failwith ("Trying to get value of unknown variable '" ^ varname ^ "'. Environment: " ^ (String.concat "," (List.map (fun (n, v) -> Printf.sprintf "%s=%i" n v) scalars))) *)
     end
  | Field (f, v) ->
     let value = evaluate_expr scalars heap v in
     let a = get_valaddr value in
     get_latest heap a f
  | Proj (i, v) ->
     begin
       let value = evaluate_expr scalars heap v in
       let a = get_valaddr value in
       let i = Int64.to_string i in
       try
	 Hashtbl.find heap (a, i)
       with
	 Not_found -> failwith "Trying to access unset heap location"
     end
  | _ -> assert false
		
(** check if there exists a path from u -field> neibor_of_u -->* v  *)
let path_check (_, pathChecker) heaps field u v = 
  if (Hashtbl.mem heaps (u, field)) then
    let neibor_of_u = Hashtbl.find heaps (u, field) in
    let neibor_of_u = get_valaddr neibor_of_u in
    (*let _ = Format.fprintf Format.std_formatter "neibor of u is %d@." neibor_of_u in*)
    PC.check_path pathChecker neibor_of_u v
  else false 

let path_connect (graph, pathChecker) u v =
  if G.mem_vertex graph u then
    PC.check_path pathChecker u v
  else
    false

let evaluate_bexpr scalars heap graph =
  function
  | Bool bexpr ->
     let value = evaluate_expr scalars heap bexpr in
     let a = get_valaddr value in
     Int64.to_int a
  | Atom (e1, rel, e2) ->
     let value1 = evaluate_expr scalars heap e1 in
     let value2 = evaluate_expr scalars heap e2 in
     if (value1 = special_value || value2 = special_value) then
       -1
     else
       if (rel_to_func rel) value1 value2 then 1 else 0
  | Link (t, endpoints, field, u, v) ->
     let t = evaluate_expr scalars heap t |> get_valaddr in
     let u = evaluate_expr scalars heap u |> get_valaddr in
     let v = evaluate_expr scalars heap v |> get_valaddr in
     (*let _ = Format.fprintf Format.std_formatter "check (t, u, v) as (%d, %d, %d)@." t u v in*)
     let result =
       path_check graph heap field u v &&
	 path_connect graph t u && path_connect graph t v && 
	   (List.for_all (fun endpoint -> 
			  let endpoint = evaluate_expr scalars heap endpoint |> get_valaddr in
			  not (path_connect graph endpoint u) && not (path_connect graph endpoint v)) endpoints) in                        
     (*let _ = Format.fprintf Format.std_formatter "Predicate %a linkability is %b@." pprint atomic result in*)
     if result || u = v then 1 else 0
  | Reach (t, endpoints, u) -> 
     let t = evaluate_expr scalars heap t |> get_valaddr in
     let u = evaluate_expr scalars heap u |> get_valaddr in
     (*let _ = Format.fprintf Format.std_formatter "check (t, u) as (%d, %d)@." t u in*)
     let result = 
       path_connect graph t u && 
	 (List.for_all (fun endpoint -> 
			let endpoint = evaluate_expr scalars heap endpoint |> get_valaddr in
			not (path_connect graph endpoint u) ) endpoints) in
     (*let _ = Format.fprintf Format.std_formatter "Predicate %a reachability is %b@." pprint atomic result in*)
     if result then 1 else 0
  | _ -> assert false

module SampleSet = Set.Make (
		       struct
			 type t = int list
			 let compare = compare
		       end);;    
  
let of_list l = 
  List.fold_left (fun res e -> SampleSet.add e res) SampleSet.empty l    
		 
let rec mini_solution k predicates pos_samples neg_samples = 
  let cands = extract k predicates in
  try 
    List.find (fun cand -> 
               List.for_all (fun pos ->
			     List.for_all (fun neg ->
					   List.exists (fun i -> List.nth pos i <> List.nth neg i) cand
					  ) neg_samples) pos_samples
              ) cands
  with Not_found ->
    mini_solution (k+1) predicates pos_samples neg_samples
		  
let to_dnf_expression pos_samples neg_samples = 
  let rec loop pos_sample neg_samples res = 
    if (List.length neg_samples = 0) then res
    else 
      (* find a column that distinguish the most number of neg_samples *)
      let (i, negs) = List.fold_left (fun (resi, resnegs) i -> 
				      let pvalue = List.nth pos_sample i in
				      let negs = List.filter (fun neg_sample -> 
							      let nvalue = List.nth neg_sample i in
							      nvalue <> pvalue
							     ) neg_samples in
				      if (List.length negs > List.length resnegs) then (i, negs)
				      else (resi, resnegs)
				     ) (-1, []) (Array.to_list (Array.init (List.length pos_sample) (fun i -> i))) in    
      let _ = assert (0 <= i && i < (List.length pos_sample)) in
      (* add the column to res *)
      let res = res @ [i] in
      (* Minus the covered neg_samples and continue this loop *)
      let neg_samples = List.filter (fun neg_sample -> 
				     List.for_all (fun neg -> neg <> neg_sample) negs    
				    ) neg_samples in
      loop pos_sample neg_samples res in 
  let pos_samples = List.map (fun pos_sample -> 
			      let res = loop pos_sample neg_samples [] in
			      let _ = assert (List.length res > 0) in 
			      List.mapi (fun i pv -> 
				    let u = List.exists (fun resi -> resi = i) res in
				    if u then 
				      if pv = 1 then `True else `False
				    else `Dontcare
				   ) pos_sample
			     ) pos_samples in
  remove_duplicates pos_samples
		    
(* We invoke Quine-McCluskey algorithm to interprete the separator *)            
let interprete solution predicates pos_samples neg_samples =
  let pos_samples = List.map (fun pos_sample -> 
			      List.map (fun i -> List.nth pos_sample i) solution
			     (*List.fold_left (fun (res,i) pos ->
            if (List.exists (fun i' -> i = i') solution) then (res @ [pos], i+1)
            else (res, i+1)
            ) ([], 0) pos_samples*)
			     ) pos_samples in
  let pos_samples = remove_duplicates pos_samples in
  let neg_samples = List.map (fun neg_sample -> 
			      List.map (fun i -> List.nth neg_sample i) solution
			     ) neg_samples in
  let neg_samples = remove_duplicates neg_samples in
  let dnfexp = to_dnf_expression pos_samples neg_samples in
  let (dnfexps, res) = Bes.auto_optimize dnfexp in    
  if (res) then
    big_or (List.map (fun dnfexp -> 
		      big_and (map_partial (fun x->x) (List.mapi (fun i pv ->
							     let predicate = List.nth predicates (List.nth solution i) in
							     if (pv = `True) then Some predicate 
							     else if (pv = `False) then Some (Not predicate)
							     else None
							    ) dnfexp))
		     ) dnfexps)
  else assert false    
              
(** Solve the shape constriants *)
let mini_invariants predicates pos_samples neg_samples = 
  (*let _ = Format.fprintf Format.std_formatter "minimizing ...@." in
    let _ = List.iter (fun predicate ->
        pprint Format.std_formatter predicate
        ) predicates in
    let _ = Format.fprintf Format.std_formatter "@.===============@." in
    let _ = List.iter (fun p ->
        List.iter (fun v ->
        Format.fprintf Format.std_formatter "%d  " v
        ) p; Format.fprintf Format.std_formatter "@.") pos_samples in
    let _ = Format.fprintf Format.std_formatter "@.=============@." in
    let _ = List.iter (fun n ->
        List.iter (fun v ->
        Format.fprintf Format.std_formatter "%d  " v
        ) n; Format.fprintf Format.std_formatter "@.") neg_samples in
    let _ = Format.fprintf Format.std_formatter "@." in *)
  if (pos_samples = [] || neg_samples = []) then []
  else if (List.exists (fun pos -> List.exists (fun neg -> 
						pos = neg) neg_samples) pos_samples) then []
  else
    (** Fixme. Prototype: a simple classification solution*)
    let indices = Array.to_list (Array.init (List.length predicates) (fun i -> i)) in
    [(mini_solution 1 indices pos_samples neg_samples)]

let symmetric_version pred = 
  match pred with
  | Link (_,_,_,v,_) 
  | Reach (_,_,v) when v = forall_vexpr -> true
  | _ -> false

(** The other predicates in Pi_O other than Pi shall be added back to Pi_I *)
let otherproperties allproperties currproperties focusproperty =
  match focusproperty with
  | Reach (x, x', u) ->
     Util.flat_mapi
       (fun i property ->
	match property with
	| Reach (y, y', v) when u <> v && x <> y && x' <> y' && List.for_all (fun i' -> i <> i') currproperties ->
	   [i]
	| _ -> []
       ) allproperties
  | _ -> []

(** Bound the free varialbes in a predicate with quantifers *)
let find_quantifiers pred = 
  let vars = vars pred in
  let u = List.mem (forall_uvar) vars in
  let v = List.mem (forall_vvar) vars in
  if (u && v) then [forall_uvar; forall_vvar]
  else if u then [forall_uvar]
  else if v then [forall_vvar]
  else []

(** Compute invariant candidates from observed data samples.
    For this, we aim to find a condition \in conditions that seems to imply (a conjunction of) properties such that all positive samples are covered.
 *)
let solve_constraints table conditions properties =
  let cache = Hashtbl.create (List.length properties) in
  let condition_len = List.length conditions in
  (* In solve_constraints t c p, t is a list of (pos/neg flag, samples) tuples
     For some samples, we have (List.map fst samples) = c @ p, i.e., the sample points are in the same order as conditions and properties.
     We look at each property \in properties predicate.
     [Not implemented: We find all similar predicates]
     For each of them, we split samples into positive and negative samples.
     We then identify other property predicates that are completely orthogonal (i.e., that concern completely different variables)
     Finally, we strip down the samples in each environment to only contains those points corresponding to condition predicates and the "other" property predicates; and extend conditions by these others.
   *)
  (* 1. work on each properties *)
  properties
  |> List.fold_left
       (fun (res, index) property ->
	if Cricket.do_log_spew () then
	  Format.fprintf Format.std_formatter "Trying to find true condition for property %a@." pprint property;
	if (Hashtbl.mem cache index || kind_of property = 0 || symmetric_version property) then res, index+1
	else
	  (* 1.5 find the other properties that are similiar (~record and tuple~) *)
	  let similarities = [index] in
	  let propertypred = big_or (List.map (fun i -> List.nth properties i) similarities) in
	  List.iter (fun i -> Hashtbl.add cache i ()) similarities;
          (* if Cricket.do_log_spew() then
	    begin
	      Cricket.log_spew (Printf.sprintf "Considered conditions: %s" (String.concat ", " (List.map string_of_cond conditions)));
	      Cricket.log_spew (Printf.sprintf "Considered properties: %s" (String.concat ", " (List.map string_of_cond properties)));
	    end; *)
	  (* 2. partition the table by the value of property *)
	  (** Fixme. Implication sample is not introduced for links *)
	  let table =
	    map_partial
	      (fun (b, data) ->
	       let row = List.map snd data in
	       match property with
	       | Link _ -> if b then Some row else None
	       | Reach _ -> Some row
	       | _ -> Some row)
	      table in
	  (* All rows where one of the similar properties is true go into the
             positive samples, everything else in the negatives. *)
	  let (pos_samples, neg_samples) =
	    List.partition (fun row ->
			    let values = List.map (fun i -> List.nth row (condition_len + i)) similarities in
			    List.exists (fun value -> value > 0) values)
			   table in

	  (* Need to add the rest of properties to the conditions and hence pos_samples and neg_samples *)
	  let otherproperties = otherproperties properties similarities property in
	  (* 3. only reserve conditions in the table *)
	  let projectToConditionsAndOthers =
	    List.map (fun sample -> (try sublist 0 (List.length conditions - 1) sample with _ -> []) @
				      List.map (fun i -> List.nth sample (condition_len+i)) otherproperties ) in
	  let pos_samples = projectToConditionsAndOthers pos_samples in
	  let neg_samples = projectToConditionsAndOthers neg_samples in
	  let conditions = conditions @ (List.map (fun i -> List.nth properties i) otherproperties) in
	  (* At this point, each sample has the same length as conditions, and we have a 1-1 correspondence between the lists *)

	  (* Now add some secret sauce as heuristic, dropping certain predicates that we feel are unneeded. *)
	  let rminds = match property with
	    | Link (d, _, _, _, _) ->
	       (* drop all predicate that is not u * v *)
	       fst (List.fold_left (fun (res, ind) condition ->
				    if (kind_of condition = 0)
                                       && (List.exists
                                             (fun var ->
					      not (var = forall_uvar || var = forall_vvar))
					     (vars condition))
				    then res @ [ind], ind+1
				    else if (kind_of condition <= (-2)) then res @ [ind], ind+1
				    else
				      ( res, ind+1)
				   ) ([], 0) conditions)
	    | Reach (d, _, _) when (kind_of property = 1) ->
	       fst (List.fold_left (fun (res, ind) condition ->
				    if (kind_of condition = 0)
                                       && (List.for_all
                                             (fun var ->
					      (var = forall_uvar || var = forall_vvar))
					     (vars condition))
				    then res @ [ind], ind+1
				    else if (kind_of condition <= (-2)) then res @ [ind], ind+1
				    else
				      (match condition with
				       | Atom (d', Eq, n) when d = d' && n = null_expr -> res @ [ind], ind+1
				       | _ -> res, ind+1)
				   ) ([], 0) conditions)
	    | property when (kind_of property = 0) -> assert false
	    | property -> (* kind_of property = -1 *)
	       (* the conditions with kind >= 0 don't need consideration *)
	       fst (List.fold_left (fun (res, ind) condition ->
				    if (kind_of condition >= 0) then res @ [ind], ind+1
				    else res, ind+1
				   ) ([], 0) conditions)  in
	  let conditions = remove_nth conditions rminds in
	  let pos_samples = List.map (fun pos_sample -> remove_nth pos_sample rminds) pos_samples |> remove_duplicates in
	  let neg_samples = List.map (fun neg_sample -> remove_nth neg_sample rminds) neg_samples |> remove_duplicates in

	  if Cricket.do_log_spew() then
	    begin
	      Cricket.log_spew (Printf.sprintf "Considered filtered conditions: %s" (String.concat ", " (List.map string_of_cond conditions)));
	      let string_of_row row = String.concat "" (List.map string_of_int row) in
	      Cricket.log_spew "Positive samples:";
	      List.iter (fun row -> Cricket.log_spew ("  " ^ string_of_row row)) pos_samples;
	      Cricket.log_spew "Negative samples:";
	      List.iter (fun row -> Cricket.log_spew ("  " ^ string_of_row row)) neg_samples;
	    end;

	  (*  Negative samples are completed *)
	  let pos_set = of_list pos_samples in
	  let neg_set = of_list neg_samples in
	  let inter_set = SampleSet.inter pos_set neg_set in
	  let separators =
	    if (SampleSet.cardinal neg_set = 0) then
	      (* This is tailored for reach (t, u) or reach (t, x) *)
	      match property with
	      | Reach (_, _, u) when kind_of property = 1 ->
		 let (preds, _) = List.fold_left (fun (res, i) condition ->
						  if (List.mem (exp_var u) (vars condition) &&
							List.for_all (fun sample -> List.nth sample i > 0) pos_samples)
						  then res @ [condition], i + 1
						  else res, i + 1
						 ) ([], 0) conditions in
		 if (preds = []) then []
		 else
		   let pre = big_and preds in
		   let foralls = find_quantifiers pre in
		   [Forall (foralls, implies (propertypred, pre))]
	      | Reach (_, _, r) -> if (SampleSet.cardinal pos_set > 0) then assert false else []
	      | Link _ -> if (SampleSet.cardinal pos_set > 0) then assert false else []
	      | _ ->
		 if (SampleSet.cardinal pos_set > 0) then
		   let foralls = find_quantifiers propertypred in
		   [Forall (foralls, propertypred)]
		 else []
	    else
	      let kind = kind_of property in
	      let pos_set = SampleSet.diff pos_set inter_set in
	      let neg_set = SampleSet.diff neg_set inter_set in
	      let pos_samples1 = SampleSet.elements pos_set in
	      let neg_samples1 = SampleSet.elements neg_set in
	      let solutions1 =
		if (kind < 0) then
		  mini_invariants conditions pos_samples1 neg_samples
		else [] in
	      let solutions2 = mini_invariants conditions pos_samples neg_samples1 in
	      let separators1 =
		List.map (fun solution ->
			  let pre = interprete solution conditions pos_samples1 neg_samples in
			  let result = implies (pre, propertypred) in
			  let foralls = find_quantifiers result in
			  Forall (foralls, result)
			 ) solutions1 in
	      let separators2 =
		List.map (fun solution ->
			  let pre = interprete solution conditions pos_samples neg_samples1 in
			  (******************************************
                        let gue, _ = List.fold_left (fun (res, index) condition ->
                            if (List.for_all (fun sample -> List.nth sample index = 1) pos_samples) then condition::res, index+1
                            else res, index+1
                            ) ([], 0) conditions in
                        let pre = big_and (pre::gue) in
			   ******************************************)
			  let result = implies (propertypred, pre) in
			  let foralls = find_quantifiers result in
			  Forall (foralls, result)
			 ) solutions2 in
	      separators1 @ separators2 in

	  if Cricket.do_log_spew () then
	    List.iter
	      (fun separator -> Format.fprintf Format.std_formatter "Solve separator = %a@." (pprint) separator)
	      separators;
	  (res @ separators, index + 1)
       ) ([], 0)
  |> fst

(** Recover the graph representation of samples.
    Then, repeat each state for all pairs of nodes, and use those to set new variables "uu" and "vv"
    (which appear in our universial quantifiers).*)       
let make_state_evaluationable (b, state) =
  (* 2.0 Fixme. scalar variables *)
  let scalars =
    Hashtbl.fold (fun varname value res -> 
                  if (varname = "nondet") then res
                  else res @ [(varname, value)])
		 state.st [] in
  (* 2.1 Collect all the nodes in the heap and heap structure for each datastructure *)
  let (nodes, graph) = heapgraph_from_state state.hp in
  let nodes = if (nodes = []) then [0L] else nodes in
  (* 2.2 Generate all pairs of nodes (including (node, node) pairs) *)
  let pairs =
    List.fold_left (fun res node -> (node, node) :: res) (pairs nodes) nodes in
  List.fold_left
    (fun res (uu, vv) ->
    
     let pathChecker = PC.create graph in
     (b, (graph, pathChecker), nodes, state.hp, ("uu", ValAddr uu)::("vv", ValAddr vv)::scalars)
     :: (b, (graph, pathChecker), nodes, state.hp, ("uu", ValAddr vv)::("vv", ValAddr uu)::scalars)
     :: res)
    [] pairs

(** Evaluate predicates on a set of observed states, and add these samples to the central store. *)
let evaluate_and_store_new_states (store : ('a, evaluated_state_samples) Hashtbl.t) atomStore (pos : 'a) sampleStates =
  let (_, (shapePreds, quantifiedCmpPreds, unquantifiedCmpPreds)) = Hashtbl.find atomStore pos in
  
  let (newQuantifiedSamples, newUnquantifiedCmpSamples) =
    List.fold_left
      (fun (newQuantifiedSamples, newUnquantifiedCmpSamples) (b, state) ->
       let (thisStateQuantSamples, thisStateUnquantCmpSamples) =
         make_state_evaluationable (b, state)
         |> List.fold_left
              (fun (qS, unQS) (b, graph, nodes, heap, scalars) ->
               let shapeSamples =
                 List.map (fun sPred -> (sPred, evaluate_bexpr scalars heap graph sPred)) shapePreds in
               let quantifiedCmpSamples =
                 List.map (fun fPred -> (fPred, evaluate_bexpr scalars heap graph fPred)) quantifiedCmpPreds in
               let unquantifiedCmpSamples =
                 List.map (fun vPred -> (vPred, evaluate_bexpr scalars heap graph vPred)) unquantifiedCmpPreds in
               ((b, shapeSamples, quantifiedCmpSamples) :: qS, (b, unquantifiedCmpSamples) :: unQS))
              ([], []) in
       ((remove_duplicates thisStateQuantSamples) @ newQuantifiedSamples,
        (remove_duplicates thisStateUnquantCmpSamples) @ newUnquantifiedCmpSamples))
      ([], []) sampleStates in
  
  let cleanedQuantifiedSamples =
    newQuantifiedSamples
    |> remove_duplicates
    |> Util.flat_map
         (fun (b, shapeSamples, quantifiedCmpSamples) ->
          quantifiedCmpSamples
          |> List.map (fun (p, t) -> if t = (-1) then [(p, 0); (p, 1)] else [(p, t)])
          |> lflap
          |> List.map (fun t -> (b, shapeSamples, t)))
    |> remove_duplicates in
  let cleanedUnquantifiedCmpSamples = remove_duplicates newUnquantifiedCmpSamples in

  let (oldQuantifiedSamples, oldUnquantifiedCmpSamples) =
    try Hashtbl.find store pos
    with Not_found -> ([], []) in
  let allQuantifiedSamples = (cleanedQuantifiedSamples @ oldQuantifiedSamples) in
  let allUnquantifiedCmpSamples = (cleanedUnquantifiedCmpSamples @ oldUnquantifiedCmpSamples) in
  
  Hashtbl.replace store pos (allQuantifiedSamples, allUnquantifiedCmpSamples)

(***********************************************************
 ************ Learn Shape-Data Invariants *******************
 ***********************************************************)
let learn (sampleStore : ('a, evaluated_state_samples) Hashtbl.t) (pos : 'a) (shapePreds, quantifiedCmpPreds, unquantifiedCmpPreds) =
  (* Get the evaluated samples *)
  let (evaluatedSamples, evaluatedUnquantifiedSamples) = Hashtbl.find sampleStore pos in

  (******************* Now Learning Shape and Data Property *********************)        
  let shapeDataInvariants =
    let samples = List.map (fun (b, s1, s2) -> (b, s2 @ s1)) evaluatedSamples in
    solve_constraints samples quantifiedCmpPreds shapePreds in
  
  (******************* Now learning quantifier free data invariant ***************)
  let dataInvariants =
    (* NOTE: This only works when the order of predicates and samples is the same.
       TODO: Redesign this to make it less fragile. *)
    let evaluatedSamples = (* sort entries for predicates with smaller kind first *)
      List.map
        (fun (b, shapePredSamples, predSamples) ->
         let sortedPredSamples =
           predSamples
           |> List.stable_sort (fun (p1, _) (p2, _) -> (kind_of p2) - (kind_of p1)) in
         (b, shapePredSamples, sortedPredSamples)) evaluatedSamples in
    (* NOTE: FRAGILE: This only works if the elements of paramKinds are bigger than
       returnKinds. Otherwise, the samples are returned in the wrong order... *)
    let getSamplesAndAtoms paramKinds returnKinds allEvaluatedSamples =
      let getKindPreds kinds =
	let (_, _, samples) = List.hd allEvaluatedSamples in
	samples |> List.filter (fun (p, _) -> List.mem (kind_of p) kinds) |> List.map fst in
      let (params, returns) = (getKindPreds paramKinds, getKindPreds returnKinds) in
      let samples =
        allEvaluatedSamples
        |> List.map
             (fun (b, _, samplesPerPred) ->
              let filteredSamples =
                samplesPerPred
                |> List.filter (fun (p, _) -> List.mem (kind_of p) (paramKinds @ returnKinds)) in
              (b, filteredSamples)) in
      (samples, params, returns) in
    let (kind12Samples, kind1Preds, kind2Preds) = getSamplesAndAtoms [-1] [-2] evaluatedSamples in
    let (kind23Samples, kind2Preds, kind3Preds) = getSamplesAndAtoms [-2] [-3] evaluatedSamples in
    
      (solve_constraints kind12Samples kind1Preds kind2Preds) (* Find "(var1 == null | var1 <> null) <== var1 == var2" invariants. *)
    @ (solve_constraints kind23Samples kind2Preds kind3Preds) (* Find "(var1 == var2 | var1 <> var2) <== var1.data <= var3" invariants. *)
    @ (solve_constraints evaluatedUnquantifiedSamples [] unquantifiedCmpPreds) in
  shapeDataInvariants @ dataInvariants
      
(** 
 Given the [errors] obtained from Verifier.check_proc,
 process them and get the correct positive/negative/implication models from them *)
let process_counterexamples simple_prog proc errors =
  let to_state model = ModelPrinting.to_stack_heap model in
  let process_error (error_pos, error_msg, model, model_list) =
    let error_msg = List.hd (Str.split (Str.regexp "\n") error_msg) in
    Cricket.log_msg ("Found error on line "
		   ^ (string_of_int error_pos.Grass.sp_start_line)
		   ^ ": " ^ error_msg);

    if Str.string_match (Str.regexp ".*invariant might not be maintained.*") error_msg 0 then
      begin
	(* Implication counter-example *)
	Cricket.log_verbose "Counterexample is implication model pair";
	[(error_pos, true, to_state model)]
      end
    else if (*error_pos.Grass.sp_start_line <= !loop_pos.Grass.sp_start_line*)
      (Str.string_match (Str.regexp ".*invariant might not hold before.*") error_msg 0) then
      begin
	Cricket.log_verbose "Counterexample is positive model";
	[(error_pos, true, to_state model)]
      end
    else if (*error_pos.Grass.sp_start_line <= !loop_pos.Grass.sp_start_line*)
      (Str.string_match (Str.regexp ".*precondition.*") error_msg 0) then
      begin
	Cricket.log_verbose "Counterexample is negative model for pre-conditions";
	let (_, proc) =
	  Grass.IdMap.fold
	    (fun id proc (id', resproc) ->
	     let name = fst (name_of_proc proc) in
             if (Str.string_match (Str.regexp (".*"^ name ^".*")) error_msg 0) then (id, proc)
	     else (id', resproc)
            ) simple_prog.prog_procs (Grass.IdMap.choose simple_prog.prog_procs) in
	assert (Str.string_match (Str.regexp (".*"^ (fst (name_of_proc proc)) ^".*")) error_msg 0);
	[(pos_of_proc proc, false, to_state model)]
      end
    else
      begin
	Cricket.log_verbose "Counterexample is negative model for post-conditions";
	[(error_pos, true, to_state model)]
      end in
  process_error (List.hd errors)

let pp_state outputter lsegs (_, state) =
  let listVars = List.map fst lsegs in
  let primitiveVars =
    Hashtbl.fold
      (fun var _ res -> if List.mem var listVars then res else var::res)
      state.st [] in
  let varAssignmentStrings =
    List.map (fun var -> Printf.sprintf "%s=%s" var (get_stack_value state var |> string_of_valu)) primitiveVars in
  outputter ("State: " ^ (String.concat ", " varAssignmentStrings));
  List.iter
    (fun (startVar, endVar) ->
     let listVals = ref [] in
     let endVal = get_stack_value state endVar in
     let curVal = ref (get_stack_value state startVar) in
     let seenAddrs = ref [] in
     while !curVal <> endVal && !curVal <> ValAddr 0L do
       if List.mem !curVal !seenAddrs then
         begin
           outputter (Printf.sprintf "Found cyclic list on address %s!" (string_of_valu !curVal));
           curVal := ValAddr 0L
         end
       else
         begin
           seenAddrs := !curVal :: !seenAddrs;
	   try
	     let value = get_heap_value state (!curVal, "data") |> get_valint in
	     listVals := (Int64.to_string value) :: !listVals;
	   with
	   | Not_found -> listVals := "X" :: !listVals;
           curVal := get_heap_value state (!curVal, "next");
         end
     done;
     outputter (Printf.sprintf "  %s->%s = [%s]" startVar endVar (String.concat "," (List.rev !listVals))))
    lsegs

let pp_state_list outputter label shapeSpecs states =
  outputter label;
  let lsegs =
    List.map
      (fun (sV, eV) -> (string_of_expr sV, string_of_expr eV))
      (find_lsegs shapeSpecs) in
  List.iter (pp_state outputter lsegs) states

let store_counterexample spl_prog learning_state (errpos, is_pre, state) =
  (* First, check if the error position is one that we know to correspond to a loop head *)
  let loopPosOpt =
    Hashtbl.fold
      (fun pos _ res ->
       if (errpos.Grass.sp_start_line = pos.Grass.sp_end_line
	   || errpos.Grass.sp_start_line = pos.Grass.sp_start_line) then
	 Some pos
       else res
      ) learning_state.observed_loop_states None in
  match loopPosOpt with
  | Some loopPos ->
    begin
      Cricket.log_verbose (Printf.sprintf "Found counterexample to loop invariant for loop at line %i" (loopPos.Grass.sp_start_line));
      if Cricket.do_log_spew() then Locust.dump_state_to_filename (Printf.sprintf "_loop_state_%i_%i" (loopPos.Grass.sp_start_line) (List.length (Hashtbl.find learning_state.observed_loop_states loopPos))) state;
      Util.listTblAddFirst learning_state.observed_loop_states loopPos (is_pre, state);
      evaluate_and_store_new_states learning_state.observed_loop_samples learning_state.loop_invariant_atoms loopPos [(is_pre, state)]; (* Evaluate new state on our predicate atoms. *)
      Hashtbl.remove learning_state.inferred_loop_invariants loopPos (* Invalidate invariant cache. *)
    end
  | _ ->
    let (proc_name, proc) = Cricket.find_proc_by_pos spl_prog errpos in
    if is_pre then
      begin
        Cricket.log_verbose (Printf.sprintf "Found counterexample to postcondition of %s" (fst proc_name));
        if Cricket.do_log_spew() then Locust.dump_state_to_filename (Printf.sprintf "_post_state_%s_%i" (fst proc_name) (List.length (Hashtbl.find learning_state.observed_post_states proc.p_name))) state;
	Util.listTblAddFirst learning_state.observed_post_states proc.p_name (true, state);
        evaluate_and_store_new_states learning_state.observed_post_samples learning_state.postcondition_atoms proc.p_name [(true, state)]; (* Evaluate new state on our predicate atoms. *)
        Hashtbl.remove learning_state.inferred_postconditions proc.p_name (* Invalidate invariant cache. *)
      end
    else
      begin
        Cricket.log_verbose (Printf.sprintf "Found counterexample to precondition of %s" (fst proc_name));
        if Cricket.do_log_spew() then Locust.dump_state_to_filename (Printf.sprintf "_pre_state_%s_%i" (fst proc_name) (List.length (Hashtbl.find learning_state.observed_pre_states proc.p_name))) state;
	Util.listTblAddFirst learning_state.observed_pre_states proc.p_name (true, state);
        evaluate_and_store_new_states learning_state.observed_pre_samples learning_state.precondition_atoms proc.p_name [(true, state)]; (* Evaluate new state on our predicate atoms. *)        
        Hashtbl.remove learning_state.inferred_preconditions proc.p_name (* Invalidate invariant cache. *)
      end
        
(** Learn invariants for loop observations.
   We iterate over all loops for which we have observations, and only learn something
   if we have no invariants for that position. Whenever we find a new counterexample
   related to the loop, we remove all learned invariants, triggering a recomputation
   here. *)
let learn_loop_invariants learning_state spl_prog =
  Hashtbl.iter
    (fun loopPos loopStates ->
     if Hashtbl.mem learning_state.inferred_loop_invariants loopPos then
       () (* We have this result cached, our work here is done. *)
     else
       let (procName, proc) = Cricket.find_proc_by_pos spl_prog loopPos in
       let (varnameToType, predicateAtoms) =
         Hashtbl.find learning_state.loop_invariant_atoms loopPos in

       if Cricket.do_log_debug () then
         begin
           let (loopShapeInvariants, _, _) = extract_shape_predicates spl_prog procName in
           let loopShapeInvariant = Hashtbl.find loopShapeInvariants loopPos in
           pp_state_list Cricket.log_debug "Observed states at loop head:" loopShapeInvariant loopStates;
         end;

       Cricket.log_msg ("Learning loop invariant for loop in " ^ (fst procName) ^ " at " ^ (Grass.string_of_src_pos loopPos) ^ " ...");
       let dataInvariant = learn learning_state.observed_loop_samples loopPos predicateAtoms in
       
       Cricket.log_msg "Learned shape-data invariant for loop:";
       if Cricket.do_log_msg () then
         if dataInvariant = [] then
           Cricket.log_msg " (None)"
         else
	   List.iter (fun inv -> Format.fprintf Format.std_formatter " %a@." pprint inv) dataInvariant;
       
       (* Convert to Spl predicates / invariants, and store away for the instrumentation bits. *)
       let (lsegs, predDeclarations, predCalls) = split3 (decode varnameToType dataInvariant) in

       learning_state.generated_predicates <- predDeclarations @ learning_state.generated_predicates;
       Hashtbl.add learning_state.inferred_loop_invariants loopPos (List.combine lsegs predCalls))
    learning_state.observed_loop_states

(** Learn preconditions.
   We iterate over all procedures for which we have pre-observations, and only learn
   something if we have no precondition for that procedure. Whenever we find a new
   counterexample that is a prestate of the procedure, we remove all related learned
   preconditions, triggering a recomputation here. *)
let learn_preconditions learning_state spl_prog =
  Hashtbl.iter
    (fun procName preStates ->
     if Hashtbl.mem learning_state.inferred_preconditions procName then
       () (* We have this result cached, our work here is done. *)
     else
       let (varnameToType, predicateAtoms) =
         Hashtbl.find learning_state.precondition_atoms procName in
       if Cricket.do_log_debug () then
         begin
           let (_, preShapeSpec, _) = extract_shape_predicates spl_prog procName in
           pp_state_list Cricket.log_debug "Observed prestates for procedure:" preShapeSpec preStates;
         end;

       Cricket.log_msg ("Learning preconditions for " ^ (fst procName) ^ " ...");
       let preconditions = learn learning_state.observed_pre_samples procName predicateAtoms in

       (* For pre-condition, filter out anything quantifier-free *)
       let cleanedPreconditions = List.filter (fun inv -> match inv with | Forall ([], inv) -> false | _ -> true) preconditions in
     
       Cricket.log_msg "Learned shape-data precondition:";
       if Cricket.do_log_msg () then
         if cleanedPreconditions = [] then
           Cricket.log_msg " (None)"
         else
           List.iter (fun inv -> Format.fprintf Format.std_formatter " %a@." pprint inv) cleanedPreconditions;
     
       let (lsegs, predDeclarations, predCalls) = split3 (decode varnameToType cleanedPreconditions) in

       learning_state.generated_predicates <- predDeclarations @ learning_state.generated_predicates;
       Hashtbl.add learning_state.inferred_preconditions procName (List.combine lsegs predCalls))
    learning_state.observed_pre_states

(** Learn postconditions.
   We iterate over all procedures for which we have post-observations, and only learn
   something if we have no postcondition for that procedure. Whenever we find a new
   counterexample that is a poststate of the procedure, we remove all related learned
   postconditions, triggering a recomputation here. *)
let learn_postconditions learning_state spl_prog =
  Hashtbl.iter
    (fun procName postStates ->
     if Hashtbl.mem learning_state.inferred_postconditions procName then
       () (* We have this result cached, our work here is done. *)
     else
       let proc = IdMap.find procName spl_prog.proc_decls in

       let (varnameToType, predicateAtoms) =
         Hashtbl.find learning_state.postcondition_atoms procName in
       if Cricket.do_log_debug () then
         begin
           let (_, _, postShapeSpec) = extract_shape_predicates spl_prog procName in
           pp_state_list Cricket.log_debug "Observed poststates for procedure:" postShapeSpec postStates;
         end;

       Cricket.log_msg ("Learning postconditions for " ^ (fst procName) ^ " ...");
       let postconditions = learn learning_state.observed_post_samples procName predicateAtoms in

       let cleanedPostconditions =
         postconditions
         |> List.filter (* Filter any inv that does not mention return value *)
	      (fun inv ->
	       if List.exists (fun var -> List.exists (fun retVar -> (fst retVar) = (fst var)) proc.p_returns) (vars inv) then
	         match inv with
	         | Forall ([], Atom (Var _, Eq, Var _)) -> false
	         | _ -> true
	       else false)
         |> List.filter
	      (fun inv -> 
	       match inv with
	       | Forall ([], Atom _) -> true
	       | Forall ([], _) -> false
	       | _ -> true) in 

       Cricket.log_msg "Learned shape-data postcondition:";
       if Cricket.do_log_msg () then
         if cleanedPostconditions = [] then
           Cricket.log_msg " (None)"
         else
           List.iter (fun inv -> Format.fprintf Format.std_formatter " %a@." pprint inv) cleanedPostconditions;

       let (lsegs, predDeclarations, predCalls) = split3 (decode varnameToType cleanedPostconditions) in

       learning_state.generated_predicates <- predDeclarations @ learning_state.generated_predicates;
       Hashtbl.add learning_state.inferred_postconditions procName (List.combine lsegs predCalls))
    learning_state.observed_post_states
  
    (*let learn_set_relations input_outputs memories spl_prog = 
        (* 1. Check out the sets of values from inputs *)
        Hashtbl.fold (fun pos (prememory, postmemory) res_decls ->
          let proc_name, proc = find_proc spl_prog pos in
                  
            let _ = Cricket.print_debug 0 "Extracting Shape predicates in procedure entries and exits ..." in
            let (_, prespecs, postspecs) = extract_shape_predicates spl_prog proc_name proc in
            
            
            (* 1.1 Firstly learn pre-conditions *)
            let _ = Cricket.print_debug 0 "Generating precondition shape-data predicates ..." in
            let (varnameToType, shapePreds, dataPreds) = generate_atomic_predicates true proc pos prespecs in
            let _ = Cricket.print_debug 0 ("Learning pre-shape-data predicates at " ^ (Grass.string_of_src_pos pos) ^   "...")  in
          let invs = learn prememory shapePreds dataPreds in
            let _ = Cricket.print_debug 0 "Learned precondition is " in
            let _ = List.iter (fun inv -> Format.fprintf Format.std_formatter "%a@." pprint inv) invs in
            
            let (presegs, predecls, precalls) = split3 (decode varnameToType invs) in
            let precalls = List.combine presegs precalls in
            
            (* 1.2  Secondly learn post-conditions *)
            let _ = Cricket.print_debug 0 "Generating postcondition shape-data predicates ..." in
            let (varnameToType, shapePreds, dataPreds) = generate_atomic_predicates true proc pos postspecs in
            let _ = Cricket.print_debug 0 ("Learning post-shape-data predicates at " ^ (Grass.string_of_src_pos pos) ^   "...")  in
          let invs = learn postmemory shapePreds dataPreds in    
            let _ = Cricket.print_debug 0 "Learned postcondition is " in
            let _ = List.iter (fun inv -> Format.fprintf Format.std_formatter "%a@." pprint inv) invs in    
            
            let (postsegs, postdecls, postcalls) = split3 (decode varnameToType invs) in
            let postcalls = List.combine postsegs postcalls in
            
            
            
            (* 2. Check out the sets of values from loops *)
            let _ = Cricket.print_debug 0 "Extracting Shape predicates in loop heads ..." in
            let (shape_predicate, _, _) = extract_shape_predicates spl_prog proc_name proc in
            
            let _ = Cricket.print_debug 0 "Generating atomic shape-data predicates ..." in
            let _ = assert (Hashtbl.mem shape_predicate pos) in
            let shape_predicate = Hashtbl.find shape_predicate pos in
            (*let locals = Hashtbl.find locals pos in*)
            let (varnameToType, shapePreds, dataPreds) = generate_atomic_predicates false proc pos shape_predicate in
             
            let _ = Cricket.print_debug 0 ("Learning shape-data predicates at " ^ (Grass.string_of_src_pos pos) ^   "...")  in
          let invs = learn memory shapePreds dataPreds in
            
            let _ = Cricket.print_debug 0 "Learned shape-data predicate is " in
            let _ = List.iter (fun inv -> Format.fprintf Format.std_formatter "%a@." pprint inv) invs in
            
        
        
            (* 3. Learn relations between inputs / loops *)
        
            (* 4. Learn relations between inputs / outputs *)
        
            (* 5. Insert inferred relations into program *)
                                        
            (* decls and calls must be inserted into the original program *)
            (*res_calls @ [(proc_name, proc, pos, calls)]*)
            let _ = 
                if (Hashtbl.mem contracttables (proc_name, proc)) then assert false
                    (*Hashtbl.replace contracttables (proc_name, proc) (Hashtbl.find pretables (proc_name, proc) @ [(precalls, postcalls)])*)
                else
                    Hashtbl.add contracttables (proc_name, proc) (precalls, postcalls) in
            res_decls @ predecls @ postdecls
      ) memories [] in
        () *)

let insert_learned_data learning_state spl_prog =
  let findUsedPredicates invs =
    List.fold_left
      (fun res inv ->
        match inv with
       | (_, (Binder (_, _, PredApp (Pred predName, _, _), _))) -> predName :: res          
       | (_, PredApp (Pred predName, _, _)) -> predName :: res
       | _ -> res) [] invs in

  (* Insert all learned things into requires/ensures and loop invariants.
     Collect all called predicates on the way, and add those later. *)
  let (usedPredicates, spl_prog) =
    Hashtbl.fold
      (fun procName preconditions (usedPredicates, spl_prog) ->
       let postconditions = Hashtbl.find learning_state.inferred_postconditions procName in
       let usedPreds = findUsedPredicates (preconditions @ postconditions) in
       let updatedProg = insert_pre_post_conditions spl_prog procName preconditions postconditions in
       (usedPreds @ usedPredicates, updatedProg))
      learning_state.inferred_preconditions ([], spl_prog) in
  let (usedPredicates, spl_prog) =
    Hashtbl.fold
      (fun loopPos loopInvariants (usedPredicates, spl_prog) ->
       let usedPreds = findUsedPredicates loopInvariants in
       let updatedProg = insert_invariants spl_prog loopPos loopInvariants in
       (usedPreds @ usedPredicates, updatedProg))
      learning_state.inferred_loop_invariants (usedPredicates, spl_prog) in

  let usedPredicates = remove_duplicates usedPredicates in
  let neededPredDecls =
    List.fold_left
      (fun neededDecls predicateDecl ->
       match predicateDecl with
       | PredDecl predDecl ->
          if List.mem predDecl.pr_name usedPredicates then
            predicateDecl :: neededDecls
          else
            neededDecls
       | _ -> failwith "Unexpected declaration found")
      [] learning_state.generated_predicates in
  extend_spl_program [] neededPredDecls [] spl_prog

let initialise_learning_state spl_prog (observed_loop_states, observed_pre_states, observed_post_states) =
  let learning_state =
    { observed_loop_states = observed_loop_states ;
      observed_pre_states  = observed_pre_states ;
      observed_post_states = observed_post_states ;

      loop_invariant_atoms = Hashtbl.create (Hashtbl.length observed_loop_states) ;
      precondition_atoms = Hashtbl.create (Hashtbl.length observed_pre_states) ;
      postcondition_atoms = Hashtbl.create (Hashtbl.length observed_post_states) ;

      observed_loop_samples = Hashtbl.create (Hashtbl.length observed_loop_states) ;
      observed_pre_samples = Hashtbl.create (Hashtbl.length observed_pre_states) ;
      observed_post_samples = Hashtbl.create (Hashtbl.length observed_post_states) ;

      inferred_loop_invariants = Hashtbl.create (Hashtbl.length observed_loop_states) ;
      inferred_preconditions = Hashtbl.create (Hashtbl.length observed_pre_states) ;
      inferred_postconditions = Hashtbl.create (Hashtbl.length observed_post_states) ;

      generated_predicates = [] ;
    } in
  
  Hashtbl.iter
    (fun loopPos loopStates ->
     let (procName, proc) = Cricket.find_proc_by_pos spl_prog loopPos in
     Cricket.log_verbose ("Initial sample processing for loop invariant in " ^ (fst procName) ^ " at " ^ (Grass.string_of_src_pos loopPos) ^ " ...");
     let (loopShapeInvariants, _, _) = extract_shape_predicates spl_prog procName in
     let loopShapeInvariant = Hashtbl.find loopShapeInvariants loopPos in
     let atoms = generate_atomic_predicates LoopInvariant proc loopPos loopShapeInvariant in
     if Cricket.do_log_spew() then
       begin
         let (_, (shapePredicates, dataPredicates, structLocalStructLocalDataCmpPreds)) = atoms in
         Cricket.log_spew (Printf.sprintf "Generated shape predicates: %s" (String.concat ", " (List.map string_of_cond shapePredicates)));
         Cricket.log_spew (Printf.sprintf "Generated data predicates: %s" (String.concat ", " (List.map string_of_cond dataPredicates)));
         Cricket.log_spew (Printf.sprintf "Generated data rel. predicates: %s" (String.concat ", " (List.map string_of_cond structLocalStructLocalDataCmpPreds)));
       end;
     Hashtbl.add learning_state.loop_invariant_atoms loopPos atoms;

     Cricket.log_verbose ("Evaluating atomic predicates on initially observed states...");
     evaluate_and_store_new_states learning_state.observed_loop_samples learning_state.loop_invariant_atoms loopPos loopStates)
    learning_state.observed_loop_states;

  Hashtbl.iter
    (fun procName preStates ->
     let proc = IdMap.find procName spl_prog.proc_decls in   
     Cricket.log_verbose ("Initial sample processing for precondition of " ^ (fst procName) ^ "...") ;
     let (_, preShapeSpec, _) = extract_shape_predicates spl_prog procName in
     let atoms = generate_atomic_predicates Precondition proc proc.p_pos preShapeSpec in
     if Cricket.do_log_spew() then
       begin
         let (_, (shapePredicates, dataPredicates, structLocalStructLocalDataCmpPreds)) = atoms in
         Cricket.log_spew (Printf.sprintf "Generated shape predicates: %s" (String.concat ", " (List.map string_of_cond shapePredicates)));
         Cricket.log_spew (Printf.sprintf "Generated data predicates: %s" (String.concat ", " (List.map string_of_cond dataPredicates)));
         Cricket.log_spew (Printf.sprintf "Generated data rel. predicates: %s" (String.concat ", " (List.map string_of_cond structLocalStructLocalDataCmpPreds)));
       end;
     Hashtbl.add learning_state.precondition_atoms procName atoms;

     Cricket.log_verbose ("Evaluating atomic predicates on initially observed states...");
     evaluate_and_store_new_states learning_state.observed_pre_samples learning_state.precondition_atoms procName preStates)
    learning_state.observed_pre_states;

  Hashtbl.iter
    (fun procName postStates ->
     let proc = IdMap.find procName spl_prog.proc_decls in   
     Cricket.log_verbose ("Initial sample processing for postcondition of " ^ (fst procName) ^ "...") ;
     let (_, _, postShapeSpec) = extract_shape_predicates spl_prog procName in
     let atoms = generate_atomic_predicates Postcondition proc proc.p_pos postShapeSpec in
     if Cricket.do_log_spew() then
       begin
         let (_, (shapePredicates, dataPredicates, structLocalStructLocalDataCmpPreds)) = atoms in
         Cricket.log_spew (Printf.sprintf "Generated shape predicates: %s" (String.concat ", " (List.map string_of_cond shapePredicates)));
         Cricket.log_spew (Printf.sprintf "Generated data predicates: %s" (String.concat ", " (List.map string_of_cond dataPredicates)));
         Cricket.log_spew (Printf.sprintf "Generated data rel. predicates: %s" (String.concat ", " (List.map string_of_cond structLocalStructLocalDataCmpPreds)));
       end;
     Hashtbl.add learning_state.postcondition_atoms procName atoms;

     Cricket.log_verbose ("Evaluating atomic predicates on initially observed states...");
     evaluate_and_store_new_states learning_state.observed_post_samples learning_state.postcondition_atoms procName postStates)
    learning_state.observed_post_states;

  learning_state
  
let learn_annotations assertion_checker spl_prog samples =
  let counter = ref 0 in  
  let rec refine_annotations learning_state =
    incr counter;
    Cricket.run_beetle (fun () -> learn_preconditions learning_state spl_prog);
    Cricket.run_beetle (fun () -> learn_postconditions learning_state spl_prog);
    Cricket.run_beetle (fun () -> learn_loop_invariants learning_state spl_prog);
    let instrumentedProg = insert_learned_data learning_state spl_prog in
    Cricket.clear_identifiers (); (* Because, who knows. Some reason. *)
    
    if Cricket.do_log_debug () then
      begin
        let prog_file = Printf.sprintf "_prog_%02i.spl" !counter in
        let out_chan = open_out prog_file in
        SplSyntax.print_spl_program out_chan instrumentedProg;
        close_out out_chan;
        Cricket.log_debug (Printf.sprintf "Written intermediate, annotated SPL program to %s" prog_file);
      end;
    
    let instrumentedProg = SplChecker.check (SplSyntax.add_alloc_decl instrumentedProg) in
    let prog = SplTranslator.to_program instrumentedProg in
    let simple_prog = Verifier.simplify prog in
    
    (* Check inferred invariant, and add counterexamples to stored data if necessary. *)
    let rec check_annotations procs =
      match procs with
      | proc :: procs ->
         begin
           Cricket.log_verbose (Printf.sprintf "Attempting verification of procedure %s" (fst (name_of_proc proc)));
           let errors = Cricket.run_grasshopper (fun () -> Verifier.check_proc simple_prog ~multiple_models:false proc) in

           match errors with
           | [] -> check_annotations procs
           | errors ->
	      begin
		process_counterexamples simple_prog proc errors
		|> List.iter (store_counterexample instrumentedProg learning_state);
		refine_annotations learning_state;
	      end
         end
      | [] -> () in
    let procs = Prog.fold_procs (fun procs p -> p :: procs) [] simple_prog in
    check_annotations procs in

  (* Process initially sampled states, then enter refinement loop. *)
  let learning_state = Cricket.run_beetle (fun () -> initialise_learning_state spl_prog samples) in
  refine_annotations learning_state;
  Cricket.log (-1) ("Program succesfully verified in " ^ (string_of_int (!counter)) ^ " iterations.")
