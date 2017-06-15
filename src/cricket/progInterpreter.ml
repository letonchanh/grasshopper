(** A module that executes spl_prog progams on heap models *)

open SplSyntax
open Util
open State
    
type evaluation_support_state =
    {
      (** Shape-data samples *)
      observed_loop_states : (pos, (bool * state) list) Hashtbl.t;
      observed_pre_states : (Grass.ident, (bool * state) list) Hashtbl.t;
      observed_post_states : (Grass.ident, (bool * state) list) Hashtbl.t;

      (** Map from id to function definition *)
      procIdToProc : (Grass.ident, proc) Hashtbl.t;
    }

let fresh_eval_support_state () =
  {
    procIdToProc = Hashtbl.create 0;
    observed_loop_states = Hashtbl.create 0;
    observed_pre_states = Hashtbl.create 0;
    observed_post_states = Hashtbl.create 0;
  }
				   

(** Create a State.state from model file *)
let state_of_model_file file_chan =
  let lexbuf = Lexing.from_channel file_chan in
  let stack_list, heap_list = ModelParser.heap ModelLexer.token lexbuf in
  let state = start_state () in
  (* Create all stack vars *)
  let process_one_var state (varname, value) =
    set_stack_value state varname value
  in
  let state = List.fold_left process_one_var state stack_list in
  (* Set hp_size to correct value. TODO improve this *)
  let max_addr = List.fold_left (fun prev_max (a, _, _) -> max prev_max a) 0L heap_list in
  let rec create_addrs state =
    if state.hp_size >= max_addr then
      state
    else
      let _, state = new_heap_value state in
      create_addrs state
  in
  let state = create_addrs state in
  (* Make all heap entries *)
  let process_one_heap_entry state (addr, fname, value) =
    set_heap_value state (addr, fname) value
  in
  let state = List.fold_left process_one_heap_entry state heap_list in
  state


let record_loop_state position state eval_support_state =
  let c = clone_state state in
  try
    let old_observations = Hashtbl.find eval_support_state.observed_loop_states position in
    Hashtbl.replace eval_support_state.observed_loop_states position (old_observations @ [(true, c)])
  with
    Not_found -> Hashtbl.add eval_support_state.observed_loop_states position [(true, c)]	     

let record_input_output_state is_pre proc state eval_support_state =
  let c = clone_state state in

  let c =
    if (not is_pre) then
    (* If it's a post-state, *)
    begin
      (* rename !ret-value! to actual return value name *)
      List.iteri
	(fun i return ->
	 let _ = assert (Hashtbl.mem c.st ("!ret-value!" ^ (string_of_int i))) in
	 (Hashtbl.replace c.st (fst return) (Hashtbl.find c.st ("!ret-value!" ^ (string_of_int i)));
	  Hashtbl.remove c.st ("!ret-value!" ^ (string_of_int i)))
	) proc.p_returns;
      (* Also project stack onto return values *)
      let name_set =
	List.fold_left
	  (fun set (name, _) -> StringSet.add name set)
	  StringSet.empty
	  proc.p_returns in
      (* Also include all other variables used in the ensures *)
      let name_set =
        List.fold_left
          (fun set contract ->
           match contract with
           | Ensures (expr, _) ->
              List.fold_left
                (fun set v -> StringSet.add (fst v) set)
                set (SplSyntax.expr_vars expr)
           | Requires _ -> set)
          name_set proc.p_contracts in
      (* Also include integer formals (e.g., lower/upper bounds *)
      let name_set =
        List.fold_left
          (fun set id ->
           match (Grass.IdMap.find id proc.p_locals).v_type with
           | IntType -> StringSet.add (fst id) set
           | _ -> set)
          name_set proc.p_formals in

      restrict_stack_to_names c name_set
    end
  else
    c
  in

  if is_pre then
    Util.listTblAddLast eval_support_state.observed_pre_states proc.p_name (true, c)
  else
    Util.listTblAddLast eval_support_state.observed_post_states proc.p_name (true, c)


(** Evaluate an expr at a given state *)
let rec eval_expr state eval_support_state = function
  | Ident ((varname, _), _) -> get_stack_value state varname, state
  | Read (Ident ((fname, _), _), expr, _) ->
     let addr, state = eval_expr state eval_support_state expr in
     get_heap_value state (addr, fname), state

  (* Address valued expressions *)
  | Null (_, _) -> ValAddr 0L, state
  | New (_, _, _) ->
     new_heap_value state

  (* Integer valued expressions *)
  | IntVal (i, _) -> ValInt i, state
  | UnaryOp (OpUPlus, exp, _) -> eval_expr state eval_support_state exp
  | UnaryOp (OpUMinus, exp, _) ->
     let v, state = eval_expr state eval_support_state exp in
     let v = get_valint v in
     ValInt (Int64.neg v), state

  | BinaryOp (exp1, OpMult, exp2, _, _) ->
     let v1, state = eval_expr state eval_support_state exp1 in
     let v2, state = eval_expr state eval_support_state exp2 in
     let v1 = get_valint v1 in
     let v2 = get_valint v2 in
     ValInt (Int64.mul v1 v2), state
  | BinaryOp (exp1, OpDiv, exp2, _, _) ->
     let v1, state = eval_expr state eval_support_state exp1 in
     let v2, state = eval_expr state eval_support_state exp2 in
     let v1 = get_valint v1 in
     let v2 = get_valint v2 in
     ValInt (Int64.div v1 v2), state
  | BinaryOp (exp1, OpPlus, exp2, _, _) ->
     let v1, state = eval_expr state eval_support_state exp1 in
     let v2, state = eval_expr state eval_support_state exp2 in
     let v1 = get_valint v1 in
     let v2 = get_valint v2 in
     ValInt (Int64.add v1 v2), state
  | BinaryOp (exp1, OpMinus, exp2, _, _) ->
     let v1, state = eval_expr state eval_support_state exp1 in
     let v2, state = eval_expr state eval_support_state exp2 in
     let v1 = get_valint v1 in
     let v2 = get_valint v2 in
     ValInt (Int64.sub v1 v2), state

  (* Boolean valued expressions *)
  | BoolVal (b, _) -> ValInt (int_of_bool b), state
  | UnaryOp (OpNot, exp, _) ->
     let v, state = eval_expr state eval_support_state exp in
     (match get_valint v with
      | 0L -> ValInt 1L, state
      | _ -> ValInt 0L, state)
  | BinaryOp (exp1, OpLt, exp2, _, _) ->
     let v1, state = eval_expr state eval_support_state exp1 in
     let v2, state = eval_expr state eval_support_state exp2 in
     let v1 = get_valint v1 in
     let v2 = get_valint v2 in
     ValInt (int_of_bool (Int64.compare v1 v2 < 0)), state
  | BinaryOp (exp1, OpGt, exp2, _, _) ->
     let v1, state = eval_expr state eval_support_state exp1 in
     let v2, state = eval_expr state eval_support_state exp2 in
     let v1 = get_valint v1 in
     let v2 = get_valint v2 in
     ValInt (int_of_bool (Int64.compare v1 v2 > 0)), state
  | BinaryOp (exp1, OpLeq, exp2, _, _) ->
     let v1, state = eval_expr state eval_support_state exp1 in
     let v2, state = eval_expr state eval_support_state exp2 in
     let v1 = get_valint v1 in
     let v2 = get_valint v2 in
     ValInt (int_of_bool (Int64.compare v1 v2 <= 0)), state
  | BinaryOp (exp1, OpGeq, exp2, _, _) ->
     let v1, state = eval_expr state eval_support_state exp1 in
     let v2, state = eval_expr state eval_support_state exp2 in
     let v1 = get_valint v1 in
     let v2 = get_valint v2 in
     ValInt (int_of_bool (Int64.compare v1 v2 >= 0)), state
  | BinaryOp (exp1, OpEq, exp2, _, _) ->
     let v1, state = eval_expr state eval_support_state exp1 in
     let v2, state = eval_expr state eval_support_state exp2 in
     ValInt (int_of_bool (v1 = v2)), state
  | BinaryOp (exp1, OpAnd, exp2, _, _) ->
     let v1, state = eval_expr state eval_support_state exp1 in
     let v1 = get_valint v1 in
     if (bool_of_int v1) then
       let v2, state = eval_expr state eval_support_state exp2 in
       let v2 = get_valint v2 in
       ValInt v2, state
     else ValInt v1, state
  | BinaryOp (exp1, OpOr, exp2, _, _) ->
     let v1, state = eval_expr state eval_support_state exp1 in
     let v1 = get_valint v1 in
     if (bool_of_int v1) then ValInt v1, state
     else
       let v2, state = eval_expr state eval_support_state exp2 in
       let v2 = get_valint v2 in
       ValInt v2, state
  (*int_of_bool ((bool_of_int v1) || (bool_of_int v2)), state*)
  | BinaryOp (exp1, OpImpl, exp2, _, _) ->
     let v1, state = eval_expr state eval_support_state exp1 in
     let v1 = get_valint v1 in
     if (bool_of_int v1) then
       let v2, state = eval_expr state eval_support_state exp2 in
       let v2 = get_valint v2 in
       ValInt v2, state
     else
       ValInt (int_of_bool true), state
  | ProcCall (f, params, _) ->
     let rvalues, state = eval_function state eval_support_state f params in
     if rvalues = [] then (ValAddr 0L, state)
     else 
       let _ = assert (List.length rvalues = 1) in
       (List.hd rvalues), state
  | _ -> failwith "Haven't written code to evaluate this kind of expr."


(** Evaluate statements on a state *)
and process_assign lhs_exp_list rhs_exp_list state eval_support_state =
  let process_one_assign state (lhs, rhs) =
    match lhs with
    | Ident ((name, _), _) ->
       (* Stack assignment *)
       let rvalue, state = (eval_expr state eval_support_state rhs) in
       let state = set_stack_value state name rvalue in
       state
    (* He Zhu *)
    | Read (Ident ((fname, _), _), expr, _) ->
       let addr, state = eval_expr state eval_support_state expr in
       let addr = get_valaddr addr in
       let rvalue, state = (eval_expr state eval_support_state rhs) in
       set_heap_value state (addr, fname) rvalue
    (*| Read (Ident ((fname, _), _), Ident ((objname, _), _), _) ->
       (* Heap assignment *)
       let addr = get_stack_value state objname in
       let rvalue, state = (eval_expr state eval_support_state rhs) in
       let state = set_heap_value state (addr, fname) rvalue in
       state*)
    | _ -> failwith "Could not recongnize this assignment."
  in
  (* He Zhu *)
  if (List.length lhs_exp_list) = 0 then 
    List.fold_left (fun state rhs -> 
		    snd (eval_expr state eval_support_state rhs)
		   ) state rhs_exp_list
  else if (List.length lhs_exp_list = List.length rhs_exp_list) then
    List.fold_left process_one_assign state (List.combine lhs_exp_list rhs_exp_list)
  else
    let _ = assert (List.length rhs_exp_list = 1) in
    let rhs = List.hd rhs_exp_list in
    match rhs with
    | ProcCall (f, params, _) ->
       let results, state = eval_function state eval_support_state f params in
       let _ = assert (List.length results = List.length lhs_exp_list) in  
       List.fold_left (fun state (lhs, rvalue) -> 
		       match lhs with
		       | Ident ((name, _), _) -> set_stack_value state name rvalue
  		       (* He Zhu *)
  		       | Read (Ident ((fname, _), _), expr, _) ->
       			  let addr, state = eval_expr state eval_support_state expr in
			  let addr = get_valaddr addr in
  			  set_heap_value state (addr, fname) rvalue
		       | _ -> assert false
		      ) state (List.combine lhs_exp_list results)
    | _ -> assert false
		  

and declare_vars var_list exprs_opt state eval_support_state =
  let declare_one_var state var =
    if var.v_type = BoolType then
      set_stack_value state (fst var.v_name) (rand_val_bool ())
    else
      set_stack_value state (fst var.v_name) (rand_val_int ())
  in
  let state = List.fold_left declare_one_var state var_list in
  match exprs_opt with
  | Some rhs_list ->
     let lhs_list = List.map
		      (fun v -> Ident (v.v_name, GrassUtil.dummy_position))
		      var_list
     in
     process_assign lhs_list rhs_list state eval_support_state
  | None -> state

and dispose exp state eval_support_state =
  let addr, state = eval_expr state eval_support_state exp in
  let addr = get_valaddr addr in
  (* remove all fields of addr in heap *)
  Hashtbl.iter
    (fun (addr1, fname) v ->
     if addr1 = addr then
       Hashtbl.remove state.hp (addr, fname))
    state.hp;

  (* find all stack variables pointing to addr and remove them from stack *)
  Hashtbl.iter
    (fun name value -> if value = ValAddr addr
		       then Hashtbl.remove state.st name)
		       (*then Hashtbl.replace state.st name (ValAddr 0L))*)
    state.st;

  (* TODO if exp is a stack var, then set it to null? *)
  state


and eval_stmts state eval_support_state stmts =
  Cricket.log_spew ("Current evaluation state: " ^ (string_of_state state));
  
  (** If the function has already returns *)
  let re = Str.regexp_string "!ret-value!" in
  let isreturned = Hashtbl.fold
		     (fun name _ res ->
		      if res then res
		      else
			(try ignore (Str.search_forward re name 0); true
			 with Not_found -> false) 
		     )
		     state.st false in
  if (isreturned) then state
  else
    begin
      if List.length stmts <> 0 then
	Cricket.log_spew ("eval_stmt: " ^ (Grass.string_of_src_pos (pos_of_stmt (List.hd stmts))));
      eval_stmts1 state eval_support_state stmts
    end

and eval_stmts1 state eval_support_state = function
  | Skip (_) :: stmts ->
     Cricket.log_spew "eval_stmt: Skip";
     eval_stmts state eval_support_state stmts
  | Block (stmts1, _) :: stmts2 ->
     Cricket.log_spew "eval_stmt: Block";
     (* Save vars in scope *)
     let varnames = get_varnames_in_stack state in
     let state = eval_stmts state eval_support_state stmts1 in
     (* Now restrict vars to saved names to get a hacky var scoping *)
     let state = restrict_stack_to_names state varnames in
     eval_stmts state eval_support_state stmts2
  | LocalVars (var_list, exprs_opt, _) :: stmts ->
     Cricket.log_spew "eval_stmt: LocalVars";
     let state = declare_vars var_list exprs_opt state eval_support_state in
     eval_stmts state eval_support_state stmts
  | Assign (lhs_exp_list, rhs_exp_list, _) :: stmts ->
     Cricket.log_spew "eval_stmt: Assign";
     let state = process_assign lhs_exp_list rhs_exp_list state eval_support_state in
     eval_stmts state eval_support_state stmts
  | If (cond, then_stmt, else_stmt, _ ) :: stmts ->
     Cricket.log_spew "eval_stmt: If";
     let cond_val, state = eval_expr state eval_support_state cond in
     if bool_of_int (get_valint cond_val) then
       eval_stmts state eval_support_state (then_stmt :: stmts)
     else
       eval_stmts state eval_support_state (else_stmt :: stmts)
  | Havoc (exp_list, _) :: stmts ->
     Cricket.log_spew "eval_stmt: Havoc";
     let rand_exp_list =
       List.fold_left
	 (fun rand_list _ ->
	  IntVal (rand_val_int () |> get_valint, GrassUtil.dummy_position)
	  :: rand_list)
	 [] exp_list
     in
     let state = process_assign exp_list rand_exp_list state eval_support_state in
     eval_stmts state eval_support_state stmts
  | Loop (contracts, prebody, cond, body, pp) :: stmts ->
     Cricket.log_spew "eval_stmt: Loop";
     let cond_val, state = eval_expr state eval_support_state cond in
     record_loop_state pp state eval_support_state;
     if bool_of_int (get_valint cond_val) then
       eval_stmts state eval_support_state (body :: (Loop (contracts, prebody, cond, body, pp)) :: stmts)
     else
       eval_stmts state eval_support_state stmts
  | Return (exp, _) :: stmts ->
     (* Cricket.log_spew "Returning ... State is ";
     Cricket.log_spew (string_of_state state);
     Cricket.log_spew "OK."; *)
     fst (List.fold_left (fun (state, i) r -> 
			  let value, state = eval_expr state eval_support_state r in
			  let _ = set_stack_value state ("!ret-value!" ^ (string_of_int i)) value in 
     			  state, i+1
			 ) (state, 0) exp)	 
  | Dispose (exp, _) :: stmts ->
     let state = dispose exp state eval_support_state in
     eval_stmts state eval_support_state stmts
  | Assume (exp, is_pure, pp) :: stmts ->
     failwith ("Don't know how to handle assume. " ^ (Grass.string_of_src_pos pp))
  | Assert (exp, is_pure, pp) :: stmts ->
     let cond_val, state = eval_expr state eval_support_state exp in
     if bool_of_int (get_valint cond_val) then
       eval_stmts state eval_support_state stmts
     else
       failwith ("Assert failed at position " ^ (Grass.string_of_src_pos pp))
  | [] -> state

(** He Zhu **)
and eval_function state eval_support_state f params =
  (* Sample the input/output behaviors of the function *)
  Cricket.log_debug ("Evaluating procedure " ^ (fst f));
  let (state, params) = List.fold_left (fun (state, vs) param -> 
					let r, s = eval_expr state eval_support_state param in
					s, vs @ [r]) (state, []) params in
  let proc = Hashtbl.find eval_support_state.procIdToProc f in 
  
  (* Save the original stack and heap *)
  let old_stack = Hashtbl.copy state.st in
  let old_heap = Hashtbl.copy state.hp in
  
  (* New stack and heap *)
  let state = {state with st = (Hashtbl.create 0)} in
  let process_one_var state formal actual =
    let formal = match formal with
      | (str, _) -> str in
    set_stack_value state ( formal) actual in
  let state = List.fold_left2 process_one_var state proc.p_formals params in
  (* Project heap to only locs reachable from stack *)
  let state = if !Config.beetle then state else restrict_heap_to_reachables state in

  (* Materialize the input state *)
  record_input_output_state true proc state eval_support_state;

  (* Execution *)
  let state = eval_stmts state eval_support_state [proc.p_body] in

  (* Materialize the output state *)
  record_input_output_state false proc state eval_support_state;
  
  (* Return and Recover the original stack and heap before return *)
  Hashtbl.iter
    (fun key valu -> Hashtbl.replace old_heap key valu)
    state.hp;
  let rvalues = 
    if (proc.p_returns = []) then []
    else
      List.mapi (fun i _ -> 
		 let _ = assert (Hashtbl.mem state.st ("!ret-value!" ^ (string_of_int i))) in
		 Hashtbl.find state.st ("!ret-value!" ^ (string_of_int i)) 
		) proc.p_returns in
  (rvalues, {
      st = old_stack;
      hp = old_heap;
      hp_size = state.hp_size;
    })


(** Run procedure [proc] in [spl_prog] on initial state [state]. *)
let evaluate spl_prog proc state =
  
  (* Construct the function id -> body mapping for inter-procedure execution *)
  let eval_support_state = fresh_eval_support_state () in
  Grass.IdMap.iter
    (fun procIdent proc -> 
     Hashtbl.replace eval_support_state.procIdToProc procIdent proc
    ) spl_prog.proc_decls;

  let result_state = eval_stmts state eval_support_state [proc.p_body] in

  (* Now project to return values and save the sample for postcondition *)
  record_input_output_state false proc result_state eval_support_state;

  eval_support_state
