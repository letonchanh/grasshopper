open Util
open Lexing
open Prog
open SplSyntax
open State
open ProgInterpreter
open Grass


(** Samples *)

(** Stores info about sample files for one run of learning loop.
    Convention: models are numbered 0 to num_X - 1, inclusive.
*)
type sample_set =
    {
      var_decls: vars;
      num_pos: int;
      num_neg: int;
      num_impl: int;

      filename_prefix: string;
    }

let create_sample_set fname_pfix var_decls =
  {
    var_decls = var_decls;
    num_pos = 0;
    num_neg = 0;
    num_impl = 0;
    filename_prefix = fname_pfix;
  }

(** Functions to dump sample_sets and ProgInterpreter.states to files *)
let dump_state_to_filename fname state =
  let chan = open_out fname in
  Hashtbl.iter
    (fun varname value ->
     match value with
     | ValInt i ->
	()
     | ValAddr a ->
	Printf.fprintf chan "[%s : A %Ld]\n" varname a)
    state.st;
  Hashtbl.iter
    (fun (addr, fname) value ->
     match value with
     | ValInt i ->
       Printf.fprintf chan "(%Ld, %s, I %Ld)\n" addr fname i
     | ValAddr a ->
        if fname = "tlparent" then (* We don't have parent pointers in Platypus trees... *)
          ()
        else if fname = "parent" then
          Printf.fprintf chan "(%Ld, %s, A 0)\n" addr fname
        else
          Printf.fprintf chan "(%Ld, %s, A %Ld)\n" addr fname a)
    state.hp;
  close_out chan

let get_pos_model_filename samples n =
  Printf.sprintf "%s_model_pos_%02d" samples.filename_prefix n

let get_neg_model_filename samples n =
  Printf.sprintf "%s_model_neg_%02d" samples.filename_prefix n

let get_impl_model_filename samples n =
  Printf.sprintf "%s_model_impl_%02d" samples.filename_prefix n

(** Dump a ProgInterpreter.state to a model file *)
let dump_state_to_pos_model samples state =
  let fname = get_pos_model_filename samples samples.num_pos in
  dump_state_to_filename fname state;
  Cricket.log_verbose ("Dumped positive model to file " ^ fname);
  {samples with num_pos = samples.num_pos + 1}

let store_model model ?(restrict_to_vars=StringSet.empty) ?(fp="") ?(repl_vals=([], [])) fname =
  let actuals = ref [] in
  if repl_vals <> ([], []) then
    begin
      let state = ModelPrinting.to_stack_heap model in
      let eval_ss = ProgInterpreter.fresh_eval_support_state () in
      let replace_val formal actual =
        let valu, state = ProgInterpreter.eval_expr state eval_ss actual in
        actuals := valu :: !actuals
      in
      List.iter2 replace_val (fst repl_vals) (snd repl_vals);
      actuals := List.rev !actuals
    end;

  let state = ModelPrinting.to_stack_heap ~footprint_set:fp model in
  (* First, replace values of vars given in repl_vals *)
  let replace_val state formal actual =
    State.set_stack_value state formal actual
  in
  let state = List.fold_left2 replace_val state (fst repl_vals) !actuals in
  (* Then, restrict stack to vars in restrict_to_vars *)
  let state = if StringSet.is_empty restrict_to_vars then state
	      else restrict_stack_to_names state restrict_to_vars
  in
  (* Also restrict the heap to locations reachable from stack *)
  let state = restrict_heap_to_reachables state in
  dump_state_to_filename fname state;
  Cricket.log_debug ("Dumped model in file " ^ fname)

(** Get and store methods for samples *)
let store_pos_model samples ?(restrict_to_vars=StringSet.empty) ?(fp="")  ?(replace_vals=([], [])) model =
  let out_filename = get_pos_model_filename samples samples.num_pos in
  store_model model ~restrict_to_vars:restrict_to_vars
	      ~fp:fp ~repl_vals:replace_vals out_filename;
  {samples with num_pos = samples.num_pos + 1}

let store_neg_model samples model =
  let out_filename = get_neg_model_filename samples samples.num_neg in
  store_model model out_filename;
  {samples with num_neg = samples.num_neg + 1}

let store_impl_models samples model1 model2 =
  let out_filename = get_impl_model_filename samples samples.num_impl in
  store_model model1 (out_filename ^ "a");
  store_model model2 (out_filename ^ "b");
  {samples with num_impl = samples.num_impl + 1}

(** Data type that stores samples seen and annotations learnt so far during learning *)
type learning_state =
    {
      observed_loop_states : (int, sample_set) Hashtbl.t ;
      observed_pre_states  : (Grass.ident, sample_set) Hashtbl.t ;
      observed_post_states : (Grass.ident, sample_set) Hashtbl.t ;

      inferred_invs : (int, expr) Hashtbl.t ;
      inferred_precons : (Grass.ident, expr) Hashtbl.t ;
      inferred_postcons : (Grass.ident, expr) Hashtbl.t ;

      (** Map loop's ending line num to starting line num *)
      loop_end_to_start : (int, int) Hashtbl.t ;
      (** Store restrict_to_vars of each postcondition *)
      vars_of_postcon : (ident, StringSet.t) Hashtbl.t;
    }

(** Convert result of Sampler.sample to a learning_state *)
let create_learning_state spl_prog (loop_sts, pre_sts, post_sts) =
  let state = {
    observed_loop_states = Hashtbl.create (Hashtbl.length loop_sts);
    observed_pre_states  = Hashtbl.create (Hashtbl.length pre_sts);
    observed_post_states = Hashtbl.create (Hashtbl.length post_sts);
    inferred_invs = Hashtbl.create (Hashtbl.length loop_sts);
    inferred_precons = Hashtbl.create (Hashtbl.length pre_sts);
    inferred_postcons = Hashtbl.create (Hashtbl.length post_sts);
    loop_end_to_start = Hashtbl.create (Hashtbl.length loop_sts);
    vars_of_postcon = Hashtbl.create (Hashtbl.length post_sts);
  }
  in

  (* Call this so that proc.p_locals has type info *)
  let spl_prog = SplChecker.resolve_names spl_prog in

  (* Fill observed_loop_states and loop_end_to_start *)
  Hashtbl.iter
    (fun pp state_list ->
      let (procName, proc) = Cricket.find_proc_by_pos spl_prog pp in
      let linum = pp.Grass.sp_start_line in
      Hashtbl.add state.loop_end_to_start pp.Grass.sp_end_line linum;
      let samples =
        List.fold_left
          (fun samples (is_pos, state) ->
	    if is_pos then dump_state_to_pos_model samples state
	    else samples (* Assumes that Sampler.sample only returns positive states *)
          )
          (create_sample_set (string_of_int linum) proc.p_locals)
          state_list
      in
      Hashtbl.add state.observed_loop_states linum samples
    )
    loop_sts;

  (* Fill observed_pre/post_states *)
  let fill_state observed_x_states x_sts pre_post =
    Hashtbl.iter
      (fun proc_id state_list ->
        let proc = Grass.IdMap.find proc_id spl_prog.proc_decls in
        let samples =
	 List.fold_left
	   (fun samples (is_pos, state) ->
	    if is_pos then dump_state_to_pos_model samples state
	    else samples (* Assumes that Sampler.sample only returns positive states *)
	   )
	   (create_sample_set ((Grass.string_of_ident proc_id) ^ "_" ^ pre_post) proc.p_locals)
	   state_list
       in
       Hashtbl.add observed_x_states proc_id samples
      )
      x_sts;
  in
  fill_state state.observed_pre_states pre_sts "pre";
  fill_state state.observed_post_states post_sts "post";

  (* Fill vars_of_postcon *)
  post_sts
  |> Hashtbl.iter (fun proc_id state_list ->
    let is_pos, first_state = List.hd state_list in
    assert is_pos;
    let vars =
      Hashtbl.fold (fun v _ vars -> StringSet.add v vars)
        first_state.st StringSet.empty
    in
    Hashtbl.add state.vars_of_postcon proc_id vars
  );

  state


(** Clean up files that have been saved, given a learning_state *)
let clean_up_learning_state state =
  let clean_up observed_x_states =
    Hashtbl.iter
      (fun _ samples ->
       for i = 0 to samples.num_pos - 1 do
	 Sys.remove (get_pos_model_filename samples i);
       done;
       for i = 0 to samples.num_neg - 1 do
	 Sys.remove (get_neg_model_filename samples i);
       done;
       for i = 0 to samples.num_impl - 1 do
	 Sys.remove ((get_impl_model_filename samples i) ^ "a");
	 Sys.remove ((get_impl_model_filename samples i) ^ "b");
       done
      )
      observed_x_states
  in
  clean_up state.observed_loop_states;
  clean_up state.observed_pre_states;
  clean_up state.observed_post_states


(** Given a Prog.program [prog] and a Prog.proc_decl [proc] with a counter-example
    Model.model [model] for a failed VC at position [pp], find the model as it would
    appear at line [lnum] *)
let get_model_at_lnum prog proc (pp, model) lnum =
  let trace = Verifier.get_trace prog proc (pp, model) in
  (* Return the first (p, model) such that p.start_line >= lnum *)
  let rec get_first_model_after_lnum lnum = function
    | (p, model) :: rest_of_trace ->
       if p.Grass.sp_start_line < lnum
       then get_first_model_after_lnum lnum rest_of_trace
       else
         begin
           Cricket.log_debug ("got model at line number "
                          ^ (string_of_int p.Grass.sp_start_line));
           model
         end
    | _ -> failwith ("get_model_at_lnum: no model at line number "
                     ^ string_of_int lnum)
  in
  get_first_model_after_lnum lnum trace


(** Take a heap model as input *) (* TODO move this util function to Cricket *)
let read_heap_from_file fname =
  let in_chan = open_in fname in
  let lexbuf = Lexing.from_channel in_chan in
  let model = ModelParser.heap ModelLexer.token lexbuf in
  close_in in_chan;
  model


(** Creates an spl procedure that checks if the model given satisfies the SL assertion [assert_expr].
Currently only checks shape properties.

Current encoding:

procedure test(all stack variables and nodes in model here)
requires P_S && P_C
{
  pure assert false;
}

*)
let add_model_and_assertion_to_prog var_decls (store, heap) assert_expr prog = (* TODO this also *)
  (* TODO: This bypasses that we don't keep types with the models (which we now would need...). *)
  let heap_size = List.length heap in
  let has_next_field = Hashtbl.create heap_size in
  let has_left_field = Hashtbl.create heap_size in
  let has_llnext_field = Hashtbl.create heap_size in
  let has_ltnext_field = Hashtbl.create heap_size in
  let has_tlleft_field = Hashtbl.create heap_size in
  let has_ttleft_field = Hashtbl.create heap_size in
  List.iter
    (fun (addr, field, _) ->
      if field = "next" then        Hashtbl.add has_next_field addr true
      else if field = "left" then   Hashtbl.add has_left_field addr true
      else if field = "llnext" then Hashtbl.add has_llnext_field addr true
      else if field = "ltnext" then Hashtbl.add has_ltnext_field addr true
      else if field = "tlleft" then Hashtbl.add has_tlleft_field addr true
      else if field = "ttleft" then Hashtbl.add has_ttleft_field addr true
      else ())
    heap;
  let get_node_type name addr =
    if Hashtbl.mem has_next_field addr then        StructType ("LNode", 0)
    else if Hashtbl.mem has_left_field addr then   StructType ("TNode", 0)
    else if Hashtbl.mem has_llnext_field addr then StructType ("LLNode", 0)
    else if Hashtbl.mem has_ltnext_field addr then StructType ("LTNode", 0)
    else if Hashtbl.mem has_tlleft_field addr then StructType ("TLNode", 0)
    else if Hashtbl.mem has_ttleft_field addr then StructType ("TTNode", 0)
    else
      match idmap_find_uniq name var_decls with
      | Some v -> v.v_type
      | None ->
        failwith (Printf.sprintf "Unknown type of variable %s at address %s" name (Int64.to_string addr)) in
  let is_non_parent = Hashtbl.create heap_size in

  let pos = GrassUtil.dummy_position in
  let mk_ident name = Ident ((name, 0), pos) in
  let mk_ident_from_id id =
    if id <> 0L then
      mk_ident ("n_" ^ (Int64.to_string id))
    else
      Null (AnyType, pos)
  in

  (* Go through heap and find all heap locations as a set of ids *)
  let node_ids =
    let add_ids_to_set id_set (n1, fld, v) =
      match v with
      | ValInt _ -> id_set
      | ValAddr n2 ->
         begin
           if not(Util.str_ends_with fld "parent") then Hashtbl.add is_non_parent n2 true;
           Int64Set.add n1 (Int64Set.add n2 id_set)
         end
    in
    List.fold_left add_ids_to_set Int64Set.empty heap
  in
  let node_ids = Int64Set.remove 0L node_ids in  (* ignore null! *)

  (* Mark values of local vars as non-parents as well. *)
  List.iter (fun (name, v) -> match v with | ValAddr addr -> Hashtbl.add is_non_parent addr true | _ -> ()) store;

  (* Create expressions whose conjunction has only the given state as model. *)
  let expr_list = [] in
  (* For each heap location id x, add "acc(n_x)" *)
  let expr_list =
    let add_var_from_id id var_list =
      if Hashtbl.mem is_non_parent id then
        PredApp (AccessPred, [Setenum (get_node_type "<no name>" id, [mk_ident_from_id id], pos)], pos)
        :: var_list
      else
        var_list
    in
    Int64Set.fold add_var_from_id node_ids expr_list
  in
  (* Process the store *)
  let expr_list =
    let add_one_var var_list (name, value) =
      (match value with
      | ValInt i ->
	 (* For each int variable in the store add "name == value" *)
	 BinaryOp (mk_ident name,
                   OpEq,
                   IntVal (i, pos),
                   BoolType,
                   pos)
      | ValAddr a ->
	 (* For each named heap location in the store add "name == n_x" *)
	 BinaryOp (mk_ident name,
                   OpEq,
                   mk_ident_from_id a,
                   BoolType,
                   pos)
      ) :: var_list
    in
    List.fold_left add_one_var expr_list store
  in
  (* Now for each field edge (id1, fld, id2), add "n_id1.fld == n_id2" *)
  let expr_list =
    let add_one_edge edge_list (id1, fld, v) =
      match v with
      | ValInt _ -> edge_list (* Ignore data values *)
      | ValAddr id2 ->
	 if id1 <> 0L && Hashtbl.mem is_non_parent id2 && fld <> "parent" then
           BinaryOp (Read(mk_ident fld, mk_ident_from_id id1, pos),
                     OpEq,
                     mk_ident_from_id id2,
                     BoolType,
                     pos)
           :: edge_list
	 else
           edge_list  (* ignore null.next = null *)
    in
    List.fold_left add_one_edge expr_list heap
  in
  (* The precondition is a conjunction of the formula describing the model, and the candidate formula *)
  let requires =
    let add_one_clause expr clause =
      BinaryOp (clause, OpSepStar, expr, BoolType, pos)
    in
    let model_form = List.fold_left add_one_clause (Emp pos) expr_list in
    Requires (BinaryOp(assert_expr, OpAnd, model_form, BoolType, pos),
	      false)
  in

  (* Collect all idents and add them as formal parameters *)
  let formals =
    let formals =
      Int64Set.fold (fun id lst -> if Hashtbl.mem is_non_parent id then ("n_" ^ (Int64.to_string id), 0) :: lst else lst) node_ids []
    in
    List.fold_left (fun lst (name, _) -> (name, 0) :: lst) formals store
  in

  let locals =
    let mk_var name addr =
      { v_name = (name, 0);
        v_type = get_node_type name addr;
        v_ghost = false;
        v_implicit = false;
        v_aux = false;
        v_pos = pos;
        v_scope = GrassUtil.global_scope;
      }
    in
    let locals =
      let add_one_var id map =
        let name = "n_" ^ (Int64.to_string id) in
        if Hashtbl.mem is_non_parent id then
          Grass.IdMap.add (name, 0) (mk_var name id) map
        else
          map
      in
      Int64Set.fold add_one_var node_ids Grass.IdMap.empty
    in
    List.fold_left
      (fun map (name, _) -> Grass.IdMap.add (name, 0) (mk_var name 0L) map)
      locals store
  in

  (* add this procedure to the program and return*)
  let dummy_proc_name = ("dummy_proc", 0) in
  let dummy_proc_decl =
    ProcDecl (
        {
          p_name = dummy_proc_name;
          p_formals = formals;
          p_returns = [];
          p_locals = locals;
          p_contracts = [requires];
          p_body = Assert (BoolVal (false, pos), true, pos);
          p_pos = pos;
        })
  in
  SplSyntax.extend_spl_program [] [dummy_proc_decl] [] prog, dummy_proc_name


let get_candidates_from_predictor samples =
  let model_filenames =
    let rec create_str num =
      if num == samples.num_pos then ""
      else (get_pos_model_filename samples num) ^ " " ^ (create_str (num + 1))
    in
    create_str 0
  in
  Cricket.run_platypus samples.var_decls model_filenames


(** Given the [errors] obtained from Verifier.check_proc,
    process them and get the correct positive/negative/implication
    models from them.

    When we find a counter-example for a particular annotation, we erase it in
    state, so that the learner knows to re-learn only that one.
*)
let process_counterexamples spl_prog simple_prog state proc errors =
  let error_pos, error_msg, model, model_list = List.hd errors in
  let error_msg = List.hd (Str.split (Str.regexp "\n") error_msg) in
  let error_lnum = error_pos.Grass.sp_start_line in
  Cricket.log_msg ("Found error on line "
                   ^ (string_of_int error_lnum)
                   ^ ": " ^ error_msg);
  let error_msg_contains str =
    Str.string_match (Str.regexp str) error_msg 0
  in
  let proc_name = name_of_proc proc in

  (* Case: precondition =/> inv *)
  if error_msg_contains ".*might not hold before entering this loop.*" then
    begin
      (* error_lnum will be same as lnum of loop *)
      Cricket.log_verbose "Counterexample is positive model for invariant";
      let samples = store_pos_model
		      (Hashtbl.find state.observed_loop_states error_lnum)
		      ~fp:"FP_LNode"
		      model
      in
      Hashtbl.replace state.observed_loop_states error_lnum samples;
      Hashtbl.remove state.inferred_invs error_lnum
    end;

  (* Case: inv =/> postcondition *)
  if error_msg_contains ".*postcondition.*not hold at this return.*" then
    begin
      Cricket.log_verbose "Counterexample is positive model for postcondition";
      (* Restrict counter-example to stack of previous counter-examples *)
      let rest_vars = Hashtbl.find state.vars_of_postcon proc_name in
      let samples =
	store_pos_model (Hashtbl.find state.observed_post_states proc_name)
			~restrict_to_vars:rest_vars
			~fp:"FP_Caller_final_LNode"
			model
      in
      Hashtbl.replace state.observed_post_states proc_name samples;
      Hashtbl.remove state.inferred_postcons proc_name
    end;

  (* Case: inv not inductive *)
  if error_msg_contains ".*invariant might not be maintained by this loop.*" then
    begin
      (* The error_pos is the loop end_line, so look up start_line in state *)
      let loop_lnum =
        Hashtbl.find state.loop_end_to_start error_pos.Grass.sp_start_line
      in
      Cricket.log_verbose @@
        "Counterexample is positive model for invariant of loop "
        ^ (string_of_int loop_lnum);

      (* Restrict model's stack to same variables as models we already have *)
      let old_samples = Hashtbl.find state.observed_loop_states loop_lnum in
      let rest_vars =
	read_heap_from_file (get_pos_model_filename old_samples 0)
	|> fst
	|> List.fold_left (fun set (name, _) -> StringSet.add name set) StringSet.empty
      in
      let samples = store_pos_model
		      (Hashtbl.find state.observed_loop_states loop_lnum)
		      ~restrict_to_vars:rest_vars
		      ~fp:"FP_LNode"
		      model in
      Hashtbl.replace state.observed_loop_states loop_lnum samples;
      Hashtbl.remove state.inferred_invs loop_lnum
    end;

  (* Case: precondition wrong *)
  if error_msg_contains ".*precondition for this call.*might not hold*" then
    begin
      Cricket.log_verbose "Counterexample is positive model for precondition";
      (* Find the procedure named in the error msg *)
      let (called_proc_id, _) =
        Grass.IdMap.fold
          (fun id proc (id', resproc) ->
            let name = name_of_proc proc |> fst in
            if (Str.string_match (Str.regexp (".* call of "^ name ^ " might .*")) error_msg 0) then
              (id, proc)
            else
              (id', resproc)
          ) simple_prog.prog_procs (Grass.IdMap.choose simple_prog.prog_procs) in
      assert (Str.string_match (Str.regexp (".*"^ (fst (called_proc_id)) ^".*")) error_msg 0);
      (* Now find the procedure call to figure out the actual params *)
      let calling_proc_id = (* HACK HACK HACK *)
        if (Util.str_ends_with (fst proc_name) "_loop") then
          (String.sub (fst proc_name) 0 (String.length (fst proc_name) - 5), 0)
        else
          proc_name in
      let called_spl_proc = Grass.IdMap.find called_proc_id spl_prog.proc_decls in
      let calling_spl_proc = Grass.IdMap.find calling_proc_id spl_prog.proc_decls in
      let actual_params =
        let params = ref [] in
        let rec process_stmt = function
          | Block (stmt_list, _) ->
            process_stmt_list stmt_list
          | If (_, stmt1, stmt2, _)
          | Loop (_, stmt1, _, stmt2, _) ->
            process_stmt stmt1;
            process_stmt stmt2
          | Assign (_, [ProcCall (iden, ps, _)], pp)
              when fst iden = fst called_proc_id && pp.Grass.sp_start_line = error_lnum ->
            params := ps
          | _ -> ()
        and process_stmt_list slist =
          List.iter process_stmt slist
        in
        process_stmt calling_spl_proc.p_body;
        !params
      in
      let formals = called_spl_proc.p_formals |> List.map fst in

      (* Restrict counter-example to formal parameters of proc *)
      let rest_vars = List.fold_left
        (fun set id -> StringSet.add id set)
        StringSet.empty
        formals
      in
      (*
      let _ = print_endline "Formals:" in
      List.iter (fun f -> print_endline ("  " ^ f)) formals;
      let _ = print_endline "Pars:" in
      List.iter (fun e -> print_endline (SplSyntax.string_of_expr e)) actual_params;
      *)
      assert (List.length formals = List.length actual_params);
      let samples =
        store_pos_model
          (Hashtbl.find state.observed_pre_states called_proc_id)
          ~fp:"FP_Caller_LNode"
          ~restrict_to_vars:rest_vars
          (* But replace the values of formal params with the actual ones *)
          ~replace_vals:(formals, actual_params)
          model
      in
      Hashtbl.replace state.observed_pre_states called_proc_id samples;
      Hashtbl.remove state.inferred_precons called_proc_id
    end;

  ()

let rec formula_contains_tree_pred = function
  | PredApp (Pred ("tree", _), _, _) -> true
  | ProcCall (("tree", _), _, _) -> true
  | BinaryOp (e1, _, e2, _, _) -> formula_contains_tree_pred e1
                                  || formula_contains_tree_pred e2
  | _ -> false


(** Goes through [spl_prog] and *replaces* all annotations with those given
    in the learning state [state],
    EXCEPT pre and post-condition of main if [main] is true.
    If [frame] is given then projects all annotations to variables in frame.
*)
let insert_annotations_into_spl_prog spl_prog ?(main=false) ?(frame=None) state =
  let rec project_expr_to_frame frame = function
    | ProcCall ((predName, _), (Ident ((head, _), _))::endE::restArgs, _)
    | PredApp (Pred (predName, _), (Ident ((head, _), _))::endE::restArgs, _)
	 when str_ends_with predName "lseg"
	      && not (StringSet.mem head frame) ->
       Emp (GrassUtil.dummy_position)
    | UnaryOp (oper, exp, pp) -> UnaryOp (oper, project_expr_to_frame frame exp, pp)
    | BinaryOp (exp1, oper, exp2, tt, pp) ->
       BinaryOp (project_expr_to_frame frame exp1, oper,
		project_expr_to_frame frame exp2, tt, pp)
    | expr -> expr
  in

  let main_proc_name, _ = Cricket.find_main_proc spl_prog in
  let insert_annotations_into_proc proc =
    let framify = match frame with
      | Some f -> project_expr_to_frame (Hashtbl.find f proc.p_name)
      | None -> (fun x -> x)
    in
    let lnum_to_invs = state.inferred_invs in
    let rec insert_invs_into_stmt = function
      | Block (stmt_list, pp) ->
	 Block (insert_invs_into_stmt_list stmt_list, pp)
      | If (e, stmt1, stmt2, pp) ->
	 If (e, insert_invs_into_stmt stmt1,
	     insert_invs_into_stmt stmt2, pp)
      | Loop (contr, stmt1, e, stmt2, pp) ->
	 let loop_lnum = pp.Grass.sp_start_line in
	 if Hashtbl.mem lnum_to_invs loop_lnum then
	   let inv = Hashtbl.find lnum_to_invs loop_lnum |> framify in
	   Loop ([Invariant (inv, false)],
		 insert_invs_into_stmt stmt1, e,
		 insert_invs_into_stmt stmt2, pp)
	 else
	   Loop (contr,
		 insert_invs_into_stmt stmt1, e,
		 insert_invs_into_stmt stmt2, pp)
      | s -> s
    and insert_invs_into_stmt_list slist =
      List.map insert_invs_into_stmt slist
    in
    let insert_pre_posts proc_contracts =
      (* Only replace contracts that we've learnt *)
      let keep_precons =
	(main && main_proc_name = proc.p_name) || (* Unless it's main *)
	  (not (Hashtbl.mem state.inferred_precons proc.p_name))
      in
      let keep_postcons =
	(main && main_proc_name = proc.p_name) || (* Unless it's main *)
	  not (Hashtbl.mem state.inferred_postcons proc.p_name)
      in
      (if not keep_precons
       then [Requires (Hashtbl.find state.inferred_precons proc.p_name
		       |> framify, false)]
       else [])
      @
	(if not keep_postcons
	 then [Ensures (Hashtbl.find state.inferred_postcons proc.p_name
			|> framify, false)]
	 else [])
      @
	List.filter
	  (function Requires _ -> keep_precons | Ensures _ -> keep_postcons)
	  proc_contracts
    in
    {proc with
      p_body = insert_invs_into_stmt proc.p_body;
      p_contracts = insert_pre_posts proc.p_contracts;
    }
  in
  {spl_prog with
    proc_decls = Grass.IdMap.map insert_annotations_into_proc spl_prog.proc_decls}

let check_cand_inv_against_samples assert_model_function cand samples =
  let rec verify_on_positives i =
    if i >= samples.num_pos then true
    else begin
        Cricket.log_debug ("Checking candidate invariant on positive model " ^ (string_of_int i));
        if assert_model_function samples.var_decls cand (get_pos_model_filename samples i) then
          begin
            Cricket.log_debug "Success: Invariant includes model."; verify_on_positives (i + 1)
          end
        else
          begin
            Cricket.log_verbose ("Failure: Invariant does not include model " ^ (string_of_int i)); false
          end
      end
  in
  let rec verify_on_negatives i =
    if i >= samples.num_neg then true
    else begin
        Cricket.log_debug ("Checking candidate invariant on negative model " ^ (string_of_int i));
        if not (assert_model_function samples.var_decls cand (get_neg_model_filename samples i)) then
          begin
            Cricket.log_debug "Success: Invariant excludes model."; verify_on_negatives (i + 1)
          end
        else
          begin
            Cricket.log_verbose ("Failure: Invariant does not include model " ^ (string_of_int i)); false
          end
      end
  in
  let rec verify_on_implications i =
    if i >= samples.num_impl then true
    else begin
        Cricket.log_debug ("Checking candidate invariant on implication model " ^ (string_of_int i));
        if assert_model_function samples.var_decls cand ((get_impl_model_filename samples i) ^ "a") then
          if assert_model_function samples.var_decls cand ((get_impl_model_filename samples i) ^ "b") then
            begin
              Cricket.log_debug "Success: Invariant includes both premise and conclusion."; verify_on_implications (i + 1)
            end
          else
            begin
              Cricket.log_verbose ("Failure: Invariant includes premise, but not conclusion of model " ^ (string_of_int i)); false
            end
        else
          begin
            Cricket.log_debug "Success: Invariant does not include premise."; verify_on_implications (i + 1)
          end
      end
  in
  (verify_on_positives 0) && (verify_on_negatives 0) && (verify_on_implications 0)


(** Calls predictor on all positive models (stored in files) and filters output.
   @return invariant consistent with all models *)
let get_consistent_candidate_inv assertion_checker samples =

  let candidates = get_candidates_from_predictor samples in

  (* Take first candidate that is consistent with neg samples *)
  let rec get_first_consistent = function
    | cand :: rest_of_cands ->
       begin
         Cricket.log_verbose ("Verifying this candidate on samples: " ^ (string_of_expr cand));
         if check_cand_inv_against_samples assertion_checker cand samples
         then cand
         else get_first_consistent rest_of_cands
       end
    | [] -> failwith "Didn't get any consistent candidates from predictor."
  in

  get_first_consistent candidates

(** Uses grasshopper to verify annotated prog. Returns true if correct *)
let verify_with_grasshopper state spl_prog = (* TODO can be moved to Cricket *)
  Cricket.clear_identifiers ();

  let spl_prog = SplChecker.check (SplSyntax.add_alloc_decl spl_prog) in
  let prog = SplTranslator.to_program spl_prog in
  let simple_prog = Verifier.simplify prog in

  let procs = Prog.fold_procs (fun procs p -> p :: procs) [] simple_prog in
  let procs = List.rev procs in

  let rec check simple_prog = function
    | proc :: procs ->
       let errors = Cricket.run_grasshopper (fun () -> Verifier.check_proc simple_prog proc) in
       begin
         match errors with
         | [] ->
	    begin
	      Cricket.log_verbose ("Successfully verified procedure " ^ (Grass.string_of_ident (name_of_proc proc)));
	      check simple_prog procs
	    end
         | errors ->
            begin
	      process_counterexamples spl_prog simple_prog state proc errors;
	      false
            end
       end
    | [] -> true
  in
  Cricket.log_msg "Checking if annotations are correct.";
  check simple_prog procs


(** Learn invariants, pre- & post-conditions for an spl_prog, given samples in a learning_state *)
let learn_annotations assertion_checker state spl_prog = (* This function can't be abstracted into cricket *)
  let learn_annot annot_printer samples_map annot_map =
    Hashtbl.iter
      (fun key samples ->
       (* Only learn if we don't already know it *)
       if not (Hashtbl.mem annot_map key) then
	 begin
	   annot_printer key;


	   let candidate_inv =
	     get_consistent_candidate_inv assertion_checker samples
	   in

	   Cricket.log_msg ("Found consistent candidate: "
			    ^ "\027[1;25m"
			    ^ (SplSyntax.string_of_expr candidate_inv)
			    ^ "\027[0m");

	   Hashtbl.add annot_map key candidate_inv
	 end
      )
      samples_map
  in

  (* Find all loop invariants *)
  learn_annot
    (fun linum -> Cricket.log_msg ("Looking at loop on line " ^ (string_of_int linum)))
    state.observed_loop_states
    state.inferred_invs;

  (* Find preconditions *)
  learn_annot
    (fun proc_id -> Cricket.log_msg ("Looking at precondition for procedure "
				     ^ (Grass.string_of_ident proc_id)))
    state.observed_pre_states
    state.inferred_precons;

  (* Find postconditions *)
  learn_annot
    (fun proc_id -> Cricket.log_msg ("Looking at postcondition for procedure "
				     ^ (Grass.string_of_ident proc_id)))
    state.observed_post_states
    state.inferred_postcons


(** Main loop of the learning process.

  Does the following:
  1. Calls predictor to get candidates
  2. filters candidates to be consistent with samples
  3. instruments spl_prog with consistent candidate
  4. runs grasshopper to check for errors
  5. if errors, process them to get more samples, and goto 1

 *)
let rec learning_loop assertion_checker state spl_prog iter =
  (* Learn all annotations *)
  learn_annotations assertion_checker state spl_prog;

  (* Insert candidate invariants into program *)
  let new_spl_prog =
    insert_annotations_into_spl_prog spl_prog state
  in
  if Cricket.do_log_debug () then print_spl_program stdout new_spl_prog;

  if not (verify_with_grasshopper state new_spl_prog) then
    (* Restart loop *)
    learning_loop assertion_checker state spl_prog (iter+1)
  else
    iter

let infer_invariant assertion_checker spl_prog pp_to_state_lists =
  (* Process the samples *)
  let state = create_learning_state spl_prog pp_to_state_lists in

  (* Call the learning loop to learn all annotations and store them in state *)
  (*Cricket.start_platypus();*)
  let iters = learning_loop assertion_checker state spl_prog 1 in
  Cricket.log_msg (Printf.sprintf "Found correct annotations in %d iterations." iters);
  (*Cricket.stop_platypus();*)

  (* If we reach here, all invariants are successfully inferred *)
  (* So clean up sample files *)
  clean_up_learning_state state;

  state
