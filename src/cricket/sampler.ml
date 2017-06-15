open ProgInterpreter
open SplSyntax
open Grass
open State


let known_predicates =
  ["lseg"; "llseg"; "ulseg"; "blseg"; "slseg"; "lslseg"; "uslseg"; "bslseg";
   "list_of_lists"; "list_of_trees"; "tree_of_lists"]

(** Find all defined variables in the preconditions *)
let get_defined_variables_in_precondition proc =
  let rec add_defined defined_vars = function
    | ProcCall ((name, _), head :: _, _)
    | PredApp (Pred (name, _), head :: _, _) when List.exists ((=) name) known_predicates ->
       head :: defined_vars
    | UnaryOp (_, exp, _) -> add_defined defined_vars exp
    | BinaryOp (exp1, _, exp2, _, _) ->
       add_defined (add_defined defined_vars exp1) exp2
    | _ -> defined_vars
  in
  List.fold_left
    (fun defined_vars contract ->
     match contract with
     | Requires (exp, _) -> add_defined defined_vars exp
     | _ -> defined_vars
    )
    []
    proc.p_contracts

let sample_via_grasshopper model_getter spl_prog proc_name proc lseg_heads list_sizes =
  (* For all lseg heads, add cardinality constraint.
     Forces a list of size at least len.
     Furthermore, if pairwise is set, requires all data fields to be pairwise disjunct integers. *)
  let input_constr head_exp (len, pairwise) =
    let pp = GrassUtil.dummy_position in
    (* the n-th next field of exp *)
    let rec read_n_of exp n =
      if n <= 0 then exp else SplSyntax.Read (Ident (("next", 0), pp), (read_n_of exp (n-1)), pp)
    in
    let length_constr =
      if len <= 0 then
	(* Force an empty list *)
	BinaryOp (head_exp,
                  OpEq,
                  Null (StructType ("LNode", 0), pp),
                  BoolType,
                  pp)
      else
	(* Force the (len - 1)-th next of head_exp to be not null *)
	UnaryOp (OpNot,
		 BinaryOp (read_n_of head_exp (len - 1),
                           OpEq,
                           Null (StructType ("LNode", 0), pp),
                           BoolType,
                           pp),
		 pp)
    in
    let rec data_n exp n =
      (* the n-th data field of exp *)
      let term = SplSyntax.Read (Ident (("data", 0), pp), read_n_of exp n, pp) in
      if (n <= 0) then
        (term, (BinaryOp (term, OpGt, IntVal (0L, pp), BoolType, pp)))
      else
        let (term', res) = data_n exp (n-1) in
        let constr =
          (* Heuristic added by He Zhu *)
          if (Random.bool() && pairwise) then
            UnaryOp (OpNot, (BinaryOp (term, OpEq, term', BoolType, pp)), pp)
          else
            (BinaryOp (term, OpEq, term', BoolType, pp)) in
        (term, BinaryOp (res, OpAnd, constr, BoolType, pp)) in

    if (!(Config.beetle)) then
      let (_, data_constr) = data_n head_exp len in
      Requires (BinaryOp (length_constr, OpAnd, data_constr, BoolType, pp), false)
    else
      Requires (length_constr, false)
  in

  (* Instrument pure assert false in the beginning *)
  let ass_pos = {GrassUtil.dummy_position with sp_start_line = -42} in
  let new_p_body =
    let ass = Assert(BoolVal (false, ass_pos),
                     true, ass_pos) in
    match proc.p_body with
    | Block (stmts, pp) -> Block (ass :: stmts, pp)
    | st -> Block(ass :: [st], GrassUtil.dummy_position)
  in

  let get_models constr =
    (* Instrument precondition with cardinality constraints *)
    let preconditions =
      List.fold_left (fun prec_list head_exp -> (input_constr head_exp constr) :: prec_list)
                     [] lseg_heads
    in
    let new_proc =
      {proc with
        p_body = new_p_body;
        p_contracts = List.rev_append preconditions proc.p_contracts}
    in
    let new_spl_prog = {spl_prog with
                         proc_decls = IdMap.add proc_name new_proc spl_prog.proc_decls
                       }
    in

    (* Get initial states from instrumented program *)
    model_getter new_spl_prog proc_name ass_pos
  in

  (* Collect initial states for different cardinalities *)
  let models = List.fold_left
                 (fun models constr -> List.rev_append (get_models constr) models)
                 [] list_sizes in
  models

let has_simple_requires proc =
  (** Check if constraint is made up of separated conjunctions of emp, lseg(x, y), and x |-> null atoms. *)
  let rec is_simple_constr = function
    | Emp _ -> true
    | ProcCall ((name, _), head :: _, _)
    | PredApp (Pred (name, _), head :: _, _) when List.exists ((=) name) known_predicates -> true
    | BinaryOp (Read (Ident ((fname, _), _), _, _), OpPts, Null _, _, _) when fname = "next" -> true
    | BinaryOp (exp1, OpSepStar, exp2, _, _) ->
       is_simple_constr exp1 && is_simple_constr exp2
    | UnaryOp (OpNot, BinaryOp (Ident _, OpEq, Null _, _, _), _)
    | UnaryOp (OpNot, BinaryOp (Null _, OpEq, Ident _, _, _), _) -> true
    | t ->
       let _ = failwith (Printf.sprintf "Requires %s not simple." (string_of_expr t)) in
       false in
  List.for_all
    (fun contract ->
     match contract with
     | Requires (exp, _) -> is_simple_constr exp
     | _ -> true)
    proc.p_contracts

let has_simple_formals proc =
  List.for_all
    (fun formalPar ->
     let localVar = Grass.IdMap.find formalPar proc.p_locals in
     match localVar.v_type with
     | IntType
     | BoolType -> true
     | StructType (name, _)
     | IdentType (name, _) when name = "LNode" || name = "TNode" || name = "LLNode" || name = "TLNode" || name = "LTNode" -> true
     | _ ->
        let _ = failwith (Printf.sprintf "Formal par (%s : %s) not simple." (fst localVar.v_name) (string_of_type localVar.v_type)) in
        false)
    proc.p_formals

let expr_has_data spl_prog proc expr =
  let node_has_data node_typ =
    match (Grass.IdMap.find node_typ spl_prog.type_decls).t_def with
    | StructTypeDef fields -> Grass.IdMap.mem ("data", 0) fields
    | _ -> false
  in

  match expr with
  | Ident (var, _) ->
     begin
       let localVar = Grass.IdMap.find var proc.p_locals in
       match localVar.v_type with
       | StructType node_type
       | IdentType node_type ->
	  node_has_data node_type
       | _ ->
	  failwith "lseg starts with variable with inappropriate type"
     end
  | _ -> failwith "lseg starts with inappropriate value"


exception SamplingHeuristicFailed
let find_list_bounds state predName predRestArgs width =
  if (predName = "blseg") || (predName = "bslseg") then
    begin
      match predRestArgs with
      | (Ident ((lb, _), _))::(Ident ((ub, _), _))::[] ->
	 if has_stack_value state lb then
	   let lbVal = Int64.to_int (get_stack_value state lb |> get_valint) in
	   if has_stack_value state ub then
	     let ubVal = Int64.to_int (get_stack_value state ub |> get_valint) in
	     (state, Some lbVal, Some ubVal)
	   else
	     let ubVal = lbVal + width in
	     let newState = set_stack_value state ub (ValInt (Int64.of_int ubVal)) in
	     (newState, Some lbVal, Some ubVal)
	 else
	   if has_stack_value state ub then
	     let ubVal = Int64.to_int (get_stack_value state ub |> get_valint) in
	     let lbVal = ubVal - width in
	     let newState = set_stack_value state lb (ValInt (Int64.of_int lbVal)) in
	     (newState, Some lbVal, Some ubVal)
	   else
	     let (lbVal, ubVal) = (-width, width) in
	     let newState = set_stack_value state lb (ValInt (Int64.of_int lbVal)) in
	     let newState = set_stack_value newState ub (ValInt (Int64.of_int ubVal)) in
	     (newState, Some lbVal, Some ubVal)
      | _ -> raise SamplingHeuristicFailed
    end
  else if predName = "uslseg" || predName = "ulseg" then
    begin
      match predRestArgs with
      | (Ident ((lb, _), _))::[] ->
	 if has_stack_value state lb then
	   let lbVal = Int64.to_int (get_stack_value state lb |> get_valint) in
	   (state, Some lbVal, None)
	 else
	   let lbVal = -width in
	   let newState = set_stack_value state lb (ValInt (Int64.of_int lbVal)) in
	   (newState, Some lbVal, None)
      | _ -> raise SamplingHeuristicFailed
    end
  else if predName = "lslseg" || predName = "llseg" then
    begin
      match predRestArgs with
      | (Ident ((ub, _), _))::[] ->
	 if has_stack_value state ub then
	   let ubVal = Int64.to_int (get_stack_value state ub |> get_valint) in
	   (state, None, Some ubVal)
	 else
	   let ubVal = width in
	   let newState = set_stack_value state ub (ValInt (Int64.of_int ubVal)) in
	   (newState, None, Some ubVal)
      | _ -> raise SamplingHeuristicFailed
    end
  else
    (state, None, None)

let rec find_defining_predicate var preds =
  match preds with
  | [] -> raise Not_found
  | pred :: rest ->
     begin
       match pred with
       | ProcCall ((name, _), (Ident ((startE, _), _)) :: _, _)
       | PredApp (Pred (name, _), (Ident ((startE, _), _)) :: _, _) when List.exists ((=) name) known_predicates && startE = var ->
	  (pred, rest)
       | BinaryOp (Read (_, Ident ((baseE, _), _), _), OpPts, _, _, _) when baseE = var ->
	  (pred, rest)
       | BinaryOp (exp1, OpSepStar, exp2, _, _) ->
	  find_defining_predicate var (exp1::exp2::rest)
       | _ ->
	  find_defining_predicate var rest
     end

let findNonNullVars =
  let rec loop acc = function
    | [] -> acc
    | pred :: rest ->
       begin
         match pred with
         | UnaryOp (OpNot, BinaryOp (Ident ((var, _), _), OpEq, Null _, _, _), _)
         | UnaryOp (OpNot, BinaryOp (Null _, OpEq, Ident ((var, _), _), _, _), _)
         | BinaryOp (Read (_, Ident ((var, _), _), _), OpPts, _, _, _) ->
            loop (var::acc) rest
         | BinaryOp (exp1, OpSepStar, exp2, _, _) ->
	    loop acc (exp1::exp2::rest)
         | _ ->
            loop acc rest
       end in
  loop []

type sortKind = AscSort | DescSort | Unsorted
let guessListElementValue lowerBound upperBound sortedness lastData listLength remainingListLength =
  match (lowerBound, upperBound) with
  | (Some lb, Some ub) ->
     begin
       match sortedness with
       | AscSort ->
          if ub > !lastData then !lastData + Random.int ((ub - !lastData) / (max 1 !remainingListLength))
          else ub
       | DescSort ->
          if lb < !lastData then !lastData - Random.int ((!lastData - lb) / (max 1 !remainingListLength))
          else lb
       | Unsorted ->
          lb + Random.int (max 1 (ub - lb))
     end
  | (Some lb, None) ->
     begin
       match sortedness with
       | AscSort ->
          !lastData + Random.int 2
       | DescSort ->
          if lb < !lastData then !lastData - Random.int ((!lastData - lb) / (max 1 !remainingListLength))
          else lb
       | Unsorted ->
          lb + Random.int (max 1 listLength)
     end
  | (None, Some ub) ->
     begin
       match sortedness with
       | AscSort ->
          if ub > !lastData then !lastData + Random.int ((ub - !lastData) / (max 1 !remainingListLength))
          else ub
       | DescSort ->
          !lastData - Random.int 2
       | Unsorted ->
          ub - Random.int (max 1 listLength)
     end
  | _ ->
     begin
       match sortedness with
       | AscSort ->
          !lastData + Random.int 3
       | DescSort ->
          !lastData - Random.int 3
       | Unsorted ->
          Random.int (max 1 listLength)
     end

(** Returns the product set ls^n *)
let rec n_cartesian_product n ls =
  if n <= 0 then
    [[]]
  else
    let res = n_cartesian_product (n - 1) ls in
    List.concat
      (List.map (fun i -> List.map (fun r -> i :: r) res) ls)

let rec generate_inner_list state length outer_addr outer_field =
  if length <= 0 then
    let new_state = set_heap_value state (outer_addr, outer_field) (ValAddr 0L) in
    new_state
  else
    let (new_node, new_state) = new_heap_value state in
    let new_addr = get_valaddr new_node in
    let new_state = set_heap_value new_state (outer_addr, outer_field) new_node in
    let new_state = generate_inner_list new_state (length - 1) new_addr "next" in
    new_state

let left_has_been_nonzero = ref false
let right_has_been_nonzero = ref false

let rec generate_inner_tree is_top state max_height outer_addr outer_field =
  if max_height <= 0 then
    let new_state = set_heap_value state (outer_addr, outer_field) (ValAddr 0L) in
    new_state
  else
    let (new_node, new_state) = new_heap_value state in
    let new_addr = get_valaddr new_node in
    let new_state = set_heap_value new_state (outer_addr, outer_field) new_node in
    let new_state =
      if not is_top then
        set_heap_value new_state (new_addr, "parent") (ValAddr outer_addr)
      else
        set_heap_value new_state (new_addr, "parent") (ValAddr 0L) in
    let left_height = if max_height <= 1 then 0 else Random.int (max_height - 1) in
    let right_height = if max_height <= 1 then 0 else Random.int (max_height - 1) in
    let (left_height, right_height) =
      if not !left_has_been_nonzero then (right_height, left_height) else (left_height, right_height) in
    let (left_height, right_height) =
      if !left_has_been_nonzero && not !right_has_been_nonzero then (right_height, left_height + 1) else (left_height, right_height) in
    left_has_been_nonzero := !left_has_been_nonzero || left_height > 0;
    right_has_been_nonzero := !right_has_been_nonzero || right_height > 0;
    let new_state = generate_inner_tree false new_state left_height new_addr "left" in
    let new_state = generate_inner_tree false new_state right_height new_addr "right" in
    new_state

let rec generate_outer_list state length parent_addr parent_field min_inner_size max_inner_size inner_generator field_prefix target =
  if length <= 0 then
    let new_state = set_heap_value state (parent_addr, parent_field) target in
    new_state
  else
    let (new_node, new_state) = new_heap_value state in
    let new_addr = get_valaddr new_node in
    let new_state = set_heap_value new_state (parent_addr, parent_field) new_node in
    let new_state = inner_generator new_state (max min_inner_size (Random.int max_inner_size)) new_addr (field_prefix ^ "data") in
    let new_state = generate_outer_list new_state (length - 1) new_addr (field_prefix ^ "next") min_inner_size max_inner_size inner_generator field_prefix target in
    new_state

let rec generate_outer_tree state max_height parent_addr parent_field min_inner_size inner_generator field_prefix =
  if max_height <= 0 then
    let new_state = set_heap_value state (parent_addr, parent_field) (ValAddr 0L) in
    new_state
  else
    let (new_node, new_state) = new_heap_value state in
    let new_addr = get_valaddr new_node in
    let new_state = set_heap_value new_state (parent_addr, parent_field) new_node in
    let new_state = set_heap_value new_state (new_addr, field_prefix ^ "parent") (ValAddr parent_addr) in
    let new_state = inner_generator new_state (max min_inner_size (Random.int max_height)) new_addr (field_prefix ^ "data") in
    let left_height = if max_height <= 1 then 0 else Random.int (max_height - 1) in
    let right_height = if max_height <= 1 then 0 else Random.int (max_height - 1) in
    let new_state = generate_outer_tree new_state left_height new_addr (field_prefix ^ "left") min_inner_size inner_generator field_prefix in
    let new_state = generate_outer_tree new_state right_height new_addr (field_prefix ^ "right") min_inner_size inner_generator field_prefix in
    new_state

(** Sample program states following hardcoded heuristics for predicates of a certain name.
    Massively unsound if the predicates definition do not match what we expect.
    Supported:
     - lseg(x, y): Singly-linked list of elements of type Node, possibly with data field
     - slseg(x, y): lseg(x, y) + sorted integer data values (ascending)
     - llseg(x, y, ub): lseg(x, y) + data values bounded from above by ub
     - lslseg(x, y, ub): slseg(x, y) + data values bounded from above by ub
     - ulseg(x, y, lb): lseg(x, y) + data values bounded from below by lb
     - uslseg(x, y, lb): slseg(x, y) + data values bounded from below by lb
     - blseg(x, y, lb, ub): lseg(x, y) + data values bounded from below by lb, from above by ub
     - bslseg(x, y, lb, ub): slseg(x, y) + blseg(x, y, lb, ub)
     - x.field |-> y: x is allocated, has field "field" whose value is y. Tries to initialise other fields of x as well.
 *)
let sample_via_heuristic spl_prog proc_name proc list_lengths =
  if not (has_simple_formals proc && has_simple_requires proc) then
    raise SamplingHeuristicFailed;
  let sample_via_heuristic_for_listlength gen_infos =
    let state = ref (start_state ()) in
    let allRequires = Util.flat_map (function | Requires (exp, _) -> [exp] | _ -> []) proc.p_contracts in
    let nonNullVars = findNonNullVars allRequires in
    (* Build hashtbl from var name to listinfo as given by gen_infos *)
    let var_to_gen_info = Hashtbl.create 0 in
    let defined_vars =
      get_defined_variables_in_precondition proc
      |> List.map
	   (function
	     | Ident ((name, _), _) -> name
	     | _ -> failwith "lseg_head was not an Ident."
	   )
    in
    List.combine defined_vars gen_infos
    |> List.iter (fun (var, gen_info) -> Hashtbl.add var_to_gen_info var gen_info);

    let rec initialiseVariable formalPar =
      let (var, _) = formalPar in
      (* Step 1: Check if our work here is already done. *)
      if has_stack_value !state var then
	get_stack_value !state var
      else
	try
          (* Step 2: Find defining predicate. *)
	  let (defPred, restPreds) = find_defining_predicate var allRequires in

	  (* Check if there is a second definition. If yes, we have no idea what's going on... *)
	  try
	    let _ = find_defining_predicate var restPreds in
	    failwith "Heuristic sampling failed: Found two defining predicates for variable."
	  with Not_found ->
	    (* Now define things! *)
	    begin
	      match defPred with
	      | ProcCall ((predName, _), startE::endE::restArgs, _)
	      | PredApp (Pred (predName, _), startE::endE::restArgs, _)
                   when predName = "list_of_lists" || predName = "list_of_trees" ->
                 begin
                   let list_length, _ = Hashtbl.find var_to_gen_info var in
                   let (inner_generator, field_prefix) =
                     if predName = "list_of_lists" then (generate_inner_list, "ll") else (generate_inner_tree true, "lt") in

                   if list_length = 0 && not (List.mem var nonNullVars) then
                     begin
                       state := set_stack_value !state var (ValAddr 0L);
		       (* If the list length is 0, then the end of the list must be null also *)
		       let _ =
			 match endE with
			 | Ident ((endVar, _), _) ->
			    state := set_stack_value !state endVar (ValAddr 0L)
			 | Null _ ->
			    ()
			 | _ -> failwith ("Unexpected last element of list_of_lists: " ^ (string_of_expr endE))
		       in
                       ValAddr 0L
                     end
                   else
		     (* Starting with startE, introduce new list *)
		     let (var_addr, new_state) = new_heap_value !state in
                     let final_addr =
		       match endE with
		       | Ident (endVar, _) -> initialiseVariable endVar
		       | Null _ -> ValAddr 0L
		       | _ -> failwith ("Unexpected last element of lseg: " ^ (string_of_expr endE)) in
		     state := set_stack_value new_state var var_addr;
		     state := inner_generator !state (max 1 list_length) (get_valaddr var_addr) (field_prefix ^ "data");
                     state := generate_outer_list !state (list_length - 1) (get_valaddr var_addr) (field_prefix ^ "next") 0 list_length inner_generator field_prefix final_addr;
		     var_addr
                 end
	      | ProcCall ((predName, _), startE::[], _)
	      | PredApp (Pred (predName, _), startE::[], _)
                   when predName = "tree_of_lists" || predName = "tree_of_trees" ->
                 begin
                   let height = max 1 (fst (Hashtbl.find var_to_gen_info var)) in
                   let (inner_generator, field_prefix) =
                     if predName = "tree_of_lists" then (generate_inner_list, "tl") else (generate_inner_tree true, "tt") in

                   (* Starting with startE, introduce new tree *)
		   let (var_addr, new_state) = new_heap_value !state in
		   state := set_stack_value new_state var var_addr;
		   state := inner_generator !state (max 1 (Random.int height)) (get_valaddr var_addr) (field_prefix ^ "data");
                   state := generate_outer_tree !state height (get_valaddr var_addr) (field_prefix ^ "left") 1 inner_generator field_prefix;
                   state := generate_outer_tree !state height (get_valaddr var_addr) (field_prefix ^ "right") 1 inner_generator field_prefix;
		   var_addr
                 end
	      | ProcCall ((predName, _), startE::endE::restArgs, _)
	      | PredApp (Pred (predName, _), startE::endE::restArgs, _) when Util.str_ends_with predName "lseg" ->
		 begin
		   let listLength, sortedness = Hashtbl.find var_to_gen_info var in
		   let sortedness = if predName = "slseg" || predName = "lslseg" || predName = "uslseg" || predName = "bslseg" then AscSort else sortedness in
		   let (new_state, lowerBound, upperBound) = find_list_bounds !state predName restArgs listLength in
		   state := new_state;

                   if listLength = 0 && not (List.mem var nonNullVars) then
                     begin
                       state := set_stack_value new_state var (ValAddr 0L);
		       (* If the list length is 0, then the end of the list must be null also *)
		       let _ =
			 match endE with
			 | Ident ((endVar, _), _) ->
			    state := set_stack_value !state endVar (ValAddr 0L)
			 | Null _ ->
			    ()
			 | _ -> failwith ("Unexpected last element of lseg: " ^ (string_of_expr endE))
		       in
                       ValAddr 0L
                     end
                   else
		     (* Starting with startE, introduce new list *)
		     let (varAddr, new_state) = new_heap_value !state in
		     state := set_stack_value new_state var varAddr;
		     let remainingListLength = ref (listLength - 1) in

                     let initialData =
                       match sortedness with
                       | AscSort -> (match lowerBound with | Some lb -> lb | _ -> -listLength)
                       | DescSort -> (match upperBound with | Some ub -> ub | _ -> listLength)
                       | _ -> 0 in
                     let lastData = ref initialData in
		     let setDataField state addr =
		       if expr_has_data spl_prog proc startE then
                         let value = guessListElementValue lowerBound upperBound sortedness lastData listLength remainingListLength in
                         lastData := value;
		         set_heap_value state (addr, "data") (ValInt (Int64.of_int value))
		       else
		         state in

		     let prevAddr = ref (get_valaddr varAddr) in
		     while !remainingListLength > 0 do
		       let (newAddr, new_state) = new_heap_value !state in
		       state := set_heap_value new_state (!prevAddr, "next") newAddr;
		       state := setDataField !state !prevAddr;
		       prevAddr := get_valaddr newAddr;
		       remainingListLength := !remainingListLength - 1;
		     done;
		     state := setDataField !state !prevAddr;
		     begin
		       match endE with
		       | Ident (endVar, _) ->
			  let endVal = initialiseVariable endVar in
			  state := set_heap_value !state (!prevAddr, "next") endVal;
		       | Null _ ->
			  state := set_heap_value !state (!prevAddr, "next") (ValAddr 0L);
		       | _ -> failwith ("Unexpected last element of lseg: " ^ (string_of_expr endE))
		     end;
		     varAddr
		 end
	      | BinaryOp (Read (Ident ((fieldName, _), _), baseVal, _), OpPts, value, _, _) ->
		 begin
		   let (varAddr, new_state) = new_heap_value !state in
		   let hasData = expr_has_data spl_prog proc baseVal in
		   state := set_stack_value new_state var varAddr;
		   let varAddrVal = get_valaddr varAddr in
		   begin
		     match value with
		     | Ident (valueVar, _) ->
			let endVal = initialiseVariable valueVar in
			state := set_heap_value !state (varAddrVal, fieldName) endVal;
		     | Null _ ->
			state := set_heap_value !state (varAddrVal, fieldName) (ValAddr 0L);
		     | _ -> failwith ("Unexpected value of |->: " ^ (string_of_expr value));
		   end;
		   if hasData && fieldName != "next" then
		     state := set_heap_value !state (varAddrVal, "data") (ValInt (Int64.of_int (Random.int 42)));
		   varAddr
		 end
	      | _ -> failwith ("Couldn't find suitable definition for " ^ var)
	    end
	with
	  (* Oh, there is no predicate. Well, then the benevolent heuristic for life decides the value should be 0. *)
	  Not_found ->
          let varValue =
            let localVar = Grass.IdMap.find formalPar proc.p_locals in
            match localVar.v_type with
            | IntType -> (ValInt 0L)
            | _ -> (ValAddr 0L) in
	  state := set_stack_value !state var varValue;
	  (ValAddr 0L) in
    List.iter (fun formalPar -> initialiseVariable formalPar |> ignore) proc.p_formals;
    (* Printf.printf "Sampled state:\n%s\n" (string_of_state !state); *)
    !state in
  let num_lists = get_defined_variables_in_precondition proc |> List.length in
  let gen_infos = n_cartesian_product num_lists list_lengths in
  List.map sample_via_heuristic_for_listlength gen_infos

let sample model_getter spl_prog is_locust max_size =
  let proc_name, proc = Cricket.find_main_proc spl_prog in

  let lseg_heads = get_defined_variables_in_precondition proc in
  Cricket.log_verbose ("Found lists starting at: " ^ (String.concat " " (List.map string_of_expr lseg_heads)));

  let models =
    try
      Cricket.log_verbose "Trying heuristic sampling..";
      if is_locust then
	sample_via_heuristic spl_prog proc_name proc
			     [(0, Unsorted);
			      (max_size, Unsorted);]
      else
	sample_via_heuristic spl_prog proc_name proc
			     [(0, Unsorted) ; (1, Unsorted) ;
			      (max_size, Unsorted);
			      (max_size, AscSort);
			      (max_size, DescSort)]
    with SamplingHeuristicFailed ->
      Cricket.log_verbose "Failed. Falling back to grasshopper sampling.";
      sample_via_grasshopper model_getter spl_prog proc_name proc lseg_heads [(0, false); (max_size, false); (max_size, true)]
      |> List.map ModelPrinting.to_stack_heap
  in
  if Cricket.do_log_debug () then
    List.iteri (fun i model -> Locust.dump_state_to_filename (Printf.sprintf "_init_model_%i" i) model) models;

  (* Execute program on initial states to get samples at loop head *)
  let observed_loop_states = Hashtbl.create 10 in
  let observed_pre_states = Hashtbl.create 10 in
  let observed_post_states = Hashtbl.create 10 in
  List.iteri
    (fun i model ->
     Cricket.log_verbose ("Interpreter starting on init model " ^ (string_of_int i));
     let eval_state = ProgInterpreter.evaluate spl_prog proc model in
     Util.listTblAppend observed_loop_states eval_state.observed_loop_states;
     Util.listTblAppend observed_pre_states eval_state.observed_pre_states;
     Util.listTblAppend observed_post_states eval_state.observed_post_states)
    models;
  (observed_loop_states, observed_pre_states, observed_post_states)
