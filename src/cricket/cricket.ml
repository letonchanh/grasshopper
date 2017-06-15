open SplSyntax
open Util
open Grass
       
(** Hack to reset identifiers used by grasshopper. This needs to be called
  before checking any spl_prog with grasshopper. *)
let clear_identifiers () =
  Hashtbl.clear GrassUtil.used_names;
  Hashtbl.clear Prog.set_ids


(** Functions to print debug info easily *)

let do_log level =
  level <= !Config.cricket_log_level

let basetime = Unix.gettimeofday ()
let platypus_time = ref 0.
let beetle_time = ref 0.
let grasshopper_time = ref 0.

let log level str =
  let padding = if level > 0 then String.make (level * 2) ' ' else "" in
  if do_log level then
    begin
      Printf.printf "%.2f:%d: %s%s\n%!" (Unix.gettimeofday () -. basetime) level padding str;
      flush_all ();
    end

let do_log_msg () = do_log 0
let do_log_verbose () = do_log 1
let do_log_debug () = do_log 2
let do_log_spew () = do_log 3

let log_msg str = log 0 str
let log_verbose str = log 1 str
let log_debug str = log 2 str
let log_spew str = log 3 str

let strict_or a b = a || b (* This is hack to force evaluation of ORs everywhere, as we sometimes care about the side-effects *)

(** Find function name / def by their positions *)
let find_proc_by_pos spl_prog (targetpos : Grass.source_position) =
  let res =
    Grass.IdMap.fold
      (fun name proc res ->
       match res with
       | Some (resname, resproc) ->
	  let pos = proc.p_pos in
	  let respos = resproc.p_pos in
	  if pos.Grass.sp_start_line <= targetpos.Grass.sp_start_line &&
	       pos.Grass.sp_start_line >= respos.Grass.sp_start_line then
	    Some (name, proc)
	  else res
       | None ->
	  let pos = proc.p_pos in
	  if pos.Grass.sp_start_line <= targetpos.Grass.sp_start_line then
	    Some (name, proc)
	  else None
      ) spl_prog.proc_decls None in

  match res with
  | Some (proc_name, proc) -> (proc_name, proc)
  | None -> failwith ("Locating procedure / loop error")

(** Find the "main" procedure in a program *)
let find_main_proc spl_prog =
  (* Currently assumes main is last procedure in file. *)
  Grass.IdMap.fold
    (fun name proc ((resname, resproc)) ->
     let pos = proc.p_pos in
     let respos = resproc.p_pos in
     if pos.Grass.sp_start_line > respos.Grass.sp_start_line then
       (name, proc)
     else
       (resname, resproc))
    spl_prog.proc_decls
    (Grass.IdMap.choose spl_prog.proc_decls)

(* Simple flow-insensitive intraprocedural sharing analysis. This assumes that things do not share at the start, which may not be correct depending on context. It's also a WILD over-approximation. If you want something better, go flow-sensitive. *)
(* TODO: Should do interprocedural by looking for calls.
   A variant of this would do for calls, which I implemented for GRASS programs (instead of spl...)
              let called_proc = IdMap.find call_cmd.call_name spl_prog.proc_decls in
              let called_var_to_sharing = go_proc called_proc in
              List.fold_left
                (fun changed (parameter, arg) ->
                 let arg_sharing_set = get_aliases (fv_term arg) in
                 let parameter_sharing_set = Hashtbl.find called_var_to_sharing_set parameter in
                 (* Look at sharing information for parameters to see if we need to join sharing information for arguments *)
                 (* This is inefficient, but there are few parameters and I'm lazy: *)
                 let changed = ref false in
                 List.iter
                   (fun (parameter', arg') ->
                    if arg <> arg' then
                      let arg'_sharing_set = get_aliases (GrassUtils.fv_term arg) in
                      let parameter'_sharing_set = Hashtbl.find called_var_to_sharing_set parameter in
                      let parameters_do_not_share = IdSet.is_empty (IdSet.inter parameter_sharing_set parameter'_sharing_set) in
                      if not parameters_do_not_share then
                        let new_arg_sharing_set = IdSet.union arg_sharing_set arg'_sharing_set in
                        let _ = List.iter (fun arg_var -> Hashtbl.replace var_to_sharing_set arg_var new_arg_sharing_set) arg_sharing_set in
                        let _ = List.iter (fun arg'_var -> Hashtbl.replace var_to_sharing_set arg'_var new_arg_sharing_set) arg'_sharing_set in
                        changed := true)
                   List.combine proc.proc_formals call_cmd.call_args;
                 (* Now look at return values *)
                 List.iter
                   (fun (return_var, lhs_var) ->
                    let return_var_sharing_set = Hashtbl.find called_var_to_sharing_set return_var in
                    let parameter_does_not_share_with_return = IdSet.is_empty (IdSet.inter parameter_sharing_set return_var_sharing_set) in
                    if not parameter_does_not_share_with_return then
                      let new_arg_sharing_set = IdSet.add lhs_var parameter_sharing_set in
                      let _ = List.iter (fun arg_var -> Hashtbl.replace var_to_sharing_set arg_var new_arg_sharing_set) in
                      changed := true)
                   List.combine proc.proc_returns call_cmd.call_lhs;
                 !changed)
                false (List.combine proc.proc_formals call_cmd.call_args);
 *)
let sharing_analysis spl_prog =
  let proc_to_var_sharing_sets = Hashtbl.create (Grass.IdMap.cardinal spl_prog.proc_decls) in
  let rec go_proc proc =
    let var_to_sharing_set = Hashtbl.create 16 in
    List.iter (fun (var, _) -> Hashtbl.add var_to_sharing_set var (StringSet.add var StringSet.empty)) proc.p_formals;
    Hashtbl.add proc_to_var_sharing_sets proc.p_name var_to_sharing_set;
    let get_shared var =
      try Hashtbl.find var_to_sharing_set var
      with | _ -> StringSet.add var StringSet.empty in
    let get_aliases vars =
      StringSet.fold (fun var res -> StringSet.union res (get_shared var)) vars StringSet.empty in
    let expr_vars expr = List.fold_left (fun res (var, _) -> StringSet.add var res) StringSet.empty (expr_vars expr) in
    let assign_helper ass_var exprs =
      let sharing_with_var = get_shared ass_var in
      let occuring_in_exprs =
        List.fold_left
          (fun res expr ->
            match expr with
            | ProcCall _ -> res (* Assume calls do not introduce new sharing. TODO: This is overly optimistic, and should be replaced by proper interprocedural analysis. *)
            | _ -> StringSet.union res (expr_vars expr))
          StringSet.empty exprs in
      let sharing_with_exprs = get_aliases occuring_in_exprs in
      let new_sharing_with_var = StringSet.union sharing_with_var sharing_with_exprs in
      let _ =
        StringSet.iter
          (fun sharing_var -> Hashtbl.replace var_to_sharing_set sharing_var new_sharing_with_var)
          sharing_with_var in
      let _ =
        StringSet.iter
          (fun sharing_var -> Hashtbl.replace var_to_sharing_set sharing_var new_sharing_with_var)
          sharing_with_exprs in
      StringSet.cardinal new_sharing_with_var > StringSet.cardinal sharing_with_var in
    let rec go_stmt stmt =
      match stmt with
      | Skip _ -> false
      | Block (stmts, _) -> List.fold_left (fun res stmt -> strict_or res (go_stmt stmt)) false stmts
      | LocalVars (lhss, rhs_opt, _) ->
         begin
           match rhs_opt with
           | Some exprs ->
	      List.fold_left
		(fun res (var, expr) -> strict_or res (assign_helper (fst var.v_name) [expr]))
                false
                (List.combine lhss exprs)
           | None -> false
         end
      | Assume _ -> false
      | Assert _ -> false
      | Assign (lhss, rhss, _) ->
         if List.length lhss > 0 then (* Ignore case of call without lhs -- TODO once we go interprocedural *)
           List.fold_left
             (fun res (lhs, rhs) ->
               let lhs_vars = expr_vars lhs in
               strict_or res (StringSet.fold (fun lhs_var res -> strict_or res (assign_helper lhs_var [rhs])) lhs_vars false))
             false
             (List.combine lhss rhss)
         else
           false
      | Havoc _ -> false (* ignore, we are flow-insensitive *)
      | Dispose _ -> false (* ignore, we are flow-insensitive *)
      | If (_, stmt1, stmt2, _) ->
         strict_or (go_stmt stmt1) (go_stmt stmt2)
      | Loop (_, prestmt, _, body, _) ->
	 if strict_or (go_stmt prestmt) (go_stmt body) then
	   let _ = go_stmt stmt in (* fixpoint step *)
	   true (* tell caller that we did something *)
	 else
	   false
      | Return (exprs, _) ->
         List.fold_left
           (fun res ((lhs_var, _), rhs) -> strict_or res (assign_helper lhs_var [rhs]))
           false
           (List.combine proc.p_returns exprs)
    in
    let _ = go_stmt proc.p_body in
    (*
    let _ = Printf.printf "Sharing sets for %s:\n" (fst proc.p_name) in
    let _ = Hashtbl.iter (fun var set -> Printf.printf " %s shares with [%s]\n" var (String.concat ", " (StringSet.elements set))) var_to_sharing_set in
     *)
    () in
  Grass.IdMap.iter (fun _ proc -> go_proc proc) spl_prog.proc_decls;
  proc_to_var_sharing_sets
    
let compute_in_frame_pars spl_prog =
  let compute_accessed_vars_in_proc proc = 
    let expr_vars expr = List.fold_left (fun res (var, _) -> StringSet.add var res) StringSet.empty (expr_vars expr) in
    let rec go_stmt acc stmt =
      match stmt with
      | Skip _ ->
         acc
      | Block (stmts, _) ->
         List.fold_left go_stmt acc stmts
      | LocalVars (_, rhss_opt, _) ->
         begin
           match rhss_opt with
           | None -> acc
           | Some exprs -> List.fold_left go_expr acc exprs
         end
      | Assume (expr, _, _)
      | Assert (expr, _, _)
      | Dispose (expr, _)
        -> go_expr acc expr
      | Assign (lhss, rhss, _)
        -> List.fold_left go_expr acc (lhss @ rhss)
      | Havoc (exprs, _)
      | Return (exprs, _)
        -> List.fold_left go_expr acc exprs
      | If (expr, stmt1, stmt2, _)
      | Loop (_, stmt1, expr, stmt2, _)
        -> go_stmt (go_stmt (go_expr acc expr) stmt2) stmt1
    and go_expr acc expr =
      match expr with
      | Null _
      | Emp _
      | IntVal _
      | BoolVal _
      | Ident _
        -> acc
      | Setenum (_, exprs, _)
      | New (_, exprs, _)
      | PredApp (_, exprs, _)
      | ProcCall (_, exprs, _)
        -> List.fold_left go_expr acc exprs
      | Read (expr1, expr2, _)
        -> go_expr (StringSet.union (expr_vars expr2) acc) expr1
      | Binder (_, _, expr, _)
      | UnaryOp (_, expr, _)
      | Annot (expr, _, _)
        -> go_expr acc expr
      | BinaryOp (expr1, _, expr2, _, _)
        -> go_expr (go_expr acc expr2) expr1
    in
    go_stmt StringSet.empty proc.p_body in
  let result = Hashtbl.create (Grass.IdMap.cardinal spl_prog.proc_decls) in
  let proc_to_var_sharing_sets = sharing_analysis spl_prog in
  Grass.IdMap.iter
    (fun proc_name proc ->
     let read_variables =
       compute_accessed_vars_in_proc proc
       (* Also add the return variables *)
       |> List.fold_right (fun (x, _) vars -> StringSet.add x vars) proc.p_returns
     in
     let var_to_sharing_set = Hashtbl.find proc_to_var_sharing_sets proc.p_name in
     let read_variables_trans_closure =
       StringSet.fold (fun var res ->
           let sharing_with_var =
             try Hashtbl.find var_to_sharing_set var
             with | _ -> StringSet.add var StringSet.empty in
           StringSet.union res sharing_with_var) read_variables StringSet.empty in
     Hashtbl.add result proc.p_name read_variables_trans_closure)
    spl_prog.proc_decls;
  result


let platypus = ref None

let start_platypus () =
  match !platypus with
  | None ->
    let base_cmd = "mono Platypus/bin/Release/Platypus.exe --insert-btwns --data-dir Platypus/data/ --tf-dir Platypus/ --prediction-number 5 --query" in
    let base_cmd = base_cmd ^ " --variable-number 2 --ds-nest-level 1" in
    log_debug ("Starting Platypus: " ^ base_cmd);
    let in_chan, out_chan = Unix.open_process base_cmd in
    platypus := Some (in_chan, out_chan)
  | Some _ -> failwith "start_platypus called when Platypus process already running."

let stop_platypus () =
  match !platypus with
  | None -> failwith "stop_platypus called when Platypus not running."
  | Some (_, out_chan) ->
    output_string out_chan ("Thank you.\n");
    flush out_chan

let query_platypus var_decls model_filenames =
  log_msg ("Calling Platypus on models in files: " ^ model_filenames);
  let in_chan, out_chan = match !platypus with
    | None -> failwith "Cricket.run_platypus: Platypus not running."
    | Some s -> s
  in
  let write str = output_string out_chan (str ^ "\n"); flush out_chan in

  let platypus_start_time = Unix.gettimeofday () in
  write "Query";
  let query_str =
    (if !Config.disj_inv then "disjunction" else "single")
    ^ " : " ^ model_filenames
  in
  log_debug (query_str);
  write query_str;
  SlParserStateHack.current_parse_vars := var_decls;
  let rec read_candidate () =
    let line = input_line in_chan |> String.trim in
    match line with
    | "Done" -> []
    | _ ->
      log_debug (Printf.sprintf "Platy returned: %s" line);
      let lexbuf = Lexing.from_string line in
      try
        let (prob, formula) = SlParser.formula SlLexer.token lexbuf in
        log_verbose (Printf.sprintf "Retrieved invariant candidate with prob %.3f from Platypus: %s" prob (SplSyntax.string_of_expr formula));
        formula :: (read_candidate ())
      with e ->
        log_verbose (Printf.sprintf "Parsing formula failed for this line: %s" line);
        log_verbose (Printf.sprintf "Failure reason: %s" (Printexc.to_string e));
        []
  in
  platypus_time := !platypus_time +. (Unix.gettimeofday())-. platypus_start_time;
  read_candidate ()

let run_platypus var_decls model_filenames =
  let platypus_base_call = "mono Platypus/bin/Release/Platypus.exe --insert-btwns --data-dir Platypus/data/ --tf-dir Platypus/ --prediction-number 5 --predict-ghp-state" in
  let base_cmd = platypus_base_call ^ " --variable-number 2 --ds-nest-level 1 " in
  log_msg ("Calling Platypus on models in files: " ^ model_filenames);
  let cmd = base_cmd ^ model_filenames in
  log_debug (cmd);
  let platypus_start_time = Unix.gettimeofday () in
  let in_chan = Unix.open_process_in cmd in
  SlParserStateHack.current_parse_vars := var_decls;
  let candidate_invariants =
    let candidate_invariants = ref [] in
    try
      while true; do
        let line = input_line in_chan in
        let lexbuf = Lexing.from_string line in
        try
          let (prob, formula) = SlParser.formula SlLexer.token lexbuf in
          log_verbose (Printf.sprintf "Retrieved invariant candidate with prob %.3f from Platypus: %s" prob (SplSyntax.string_of_expr formula));
          candidate_invariants := formula :: !candidate_invariants
        with e ->
          log_verbose (Printf.sprintf "Parsing formula failed for this line: %s" line);
          log_verbose (Printf.sprintf "Failure reason: %s" (Printexc.to_string e))
      done;
      !candidate_invariants
    with End_of_file ->
      let _ = Unix.close_process_in in_chan in
      List.rev !candidate_invariants in
  platypus_time := !platypus_time +. (Unix.gettimeofday())-. platypus_start_time;
  candidate_invariants

let run_grasshopper func =
  let grasshopper_start_time = Unix.gettimeofday () in
  let res = func () in
  grasshopper_time := !grasshopper_time +. (Unix.gettimeofday()) -. grasshopper_start_time ;
  res

let run_beetle func =
  let beetle_start_time = Unix.gettimeofday () in
  let res = func () in
  beetle_time := !beetle_time +. (Unix.gettimeofday()) -. beetle_start_time ;
  res
