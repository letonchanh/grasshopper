open Form
open FormUtil
open Programs


(** Coarse-grained frame inference *)
let annotate_modifies prog =
  let rec pm prog = function
    | Loop (lc, pp) ->
        let has_new1, prebody1 = pm prog lc.loop_prebody in
        let has_new2, postbody1 = pm prog lc.loop_postbody in
        let lc1 = {lc with loop_prebody = prebody1; loop_postbody = postbody1} in
        let mods = IdSet.union (modifies prebody1) (modifies postbody1) in
        let pp1 = {pp with pp_modifies = mods} in
        has_new1 || has_new2, Loop (lc1, pp1)
    | Choice (cs, pp) ->
        let has_new, mods, cs1 = 
          List.fold_right 
            (fun c (has_new, mods, cs1) ->
              let has_new1, c1 = pm prog c in
              has_new1 || has_new, IdSet.union (modifies c1) mods, c1 :: cs1)
            cs (false, IdSet.empty, [])
        in
        let pp1 = {pp with pp_modifies = mods} in
        has_new, Choice (cs1, pp1)
    | Seq (cs, pp) ->
        let has_new, mods, cs1 = 
          List.fold_right 
            (fun c (has_new, mods, cs1) ->
              let has_new1, c1 = pm prog c in
              has_new1 || has_new, IdSet.union (modifies c1) mods, c1 :: cs1)
            cs (false, IdSet.empty, [])
        in
        let pp1 = {pp with pp_modifies = mods} in
        has_new, Seq (cs1, pp1)
    | Basic (ac, pp) ->
        let mods = basic_modifies prog ac in
        let has_new = IdSet.subset mods pp.pp_modifies in
        let pp1 = {pp with pp_modifies = mods} in
        has_new, Basic (ac, pp1)
  in
  let rec pm_prog prog = 
    let procs = procs prog in
    let has_new, procs1 =
      List.fold_left 
        (fun (has_new, procs1) proc ->
          match proc.proc_body with
          | Some body ->
              let has_new1, body1 = pm prog body in
              let proc1 = {proc with proc_body = Some body1} in
              (has_new || has_new1, proc1 :: procs1)
          | None -> (has_new, proc :: procs1))
        (false, []) procs
    in 
    let procs2 = 
      List.fold_left 
      (fun procs2 proc -> IdMap.add proc.proc_name proc procs2) 
      IdMap.empty procs1
    in
    let prog1 = {prog with prog_procs = procs2} in
    if has_new then prog1 else pm_prog prog1
  in
  pm_prog prog

let alloc_id = mk_ident "Alloc"

let alloc_set = mk_free_const ~srt:(Set Loc) alloc_id

let init_alloc_id = mk_ident "InitAlloc"

let init_alloc_set = mk_free_const ~srt:(Set Loc) init_alloc_id

let alloc_callee_id = mk_ident "PostAllocCallee"

let alloc_callee_set = mk_free_const ~srt:(Set Loc) alloc_callee_id

let init_alloc_callee_id = mk_ident "InitAllocCallee"

let init_alloc_callee_set = mk_free_const ~srt:(Set Loc) init_alloc_callee_id

let frame_id = mk_ident "AllocCaller"

let frame_set = mk_free_const ~srt:(Set Loc) frame_id

let elim_sl prog =
  let compile_proc proc =
    (** add auxiliary set variables *)
    let locals =
      List.fold_left (fun locals id ->
        let decl = 
          { var_name = id;
            var_orig_name = name id;
            var_sort = Set Loc;
            var_is_ghost = true;
            var_is_aux = true;
            var_pos = proc.proc_pos;
          }
        in
        IdMap.add id decl locals)
        proc.proc_locals 
        [alloc_id; init_alloc_id; frame_id; alloc_callee_id; init_alloc_callee_id]
    in
    let returns = init_alloc_id :: alloc_id :: proc.proc_returns in
    let formals = frame_id :: proc.proc_formals in
    let convert_sl_form sfs name =
      let fs, aux = 
        List.fold_right (fun sf (fs, aux) -> 
          match sf.spec_form, aux with
          | SL f, None -> f :: fs, Some (sf.spec_name, sf.spec_msg, sf.spec_pos)
          | SL f, Some (_, _, p) -> 
              f :: fs, Some (sf.spec_name, sf.spec_msg, merge_src_positions p sf.spec_pos)
          | _ -> fs, aux)
          sfs ([], None)
      in
      let name, msg, pos = Util.safe_unopt (name, None, dummy_position) aux in
      SlUtil.mk_sep_lst fs, name, msg, pos
    in
    (* compile SL precondition *)
    let sl_precond, other_precond = List.partition is_sl_spec proc.proc_precond in
    let precond, footprint =
      let f, name, msg, pos = convert_sl_form sl_precond "precondition" in
      let f_in_frame = ToGrass.to_grass_contained frame_id f in
      let f_notin_frame = ToGrass.to_grass_not_contained frame_id f in
      let f_eq_init_alloc = ToGrass.to_grass init_alloc_id f in
      let precond = mk_checked_spec_form (FOL f_in_frame) name msg pos in
      { precond with spec_form_negated = Some f_notin_frame },
      mk_free_spec_form (FOL f_eq_init_alloc) "footprint" None pos
    in
    (* compile SL postcondition *)
    let sl_postcond, other_postcond = List.partition is_sl_spec proc.proc_postcond in
    let postcond =
      let f, name, msg, pos = convert_sl_form sl_postcond "postcondition" in
      let f_eq_alloc = ToGrass.to_grass alloc_id f in
      let f_neq_alloc = ToGrass.to_grass_negated alloc_id f in
      let postcond = mk_spec_form (FOL f_eq_alloc) name msg pos in
      { postcond with spec_form_negated = Some f_neq_alloc }
    in
    (* generate frame condition *) 
    let framecond = 
      let frame_wo_alloc = mk_diff frame_set init_alloc_set in
      let mk_framecond f = mk_free_spec_form (FOL f) "framecondition" None postcond.spec_pos in
      (* null in not allocated *)
      mk_framecond (mk_not (smk_elem mk_null alloc_set)) ::
      (* initial footprint is contained in frame *)
      mk_framecond (mk_subseteq init_alloc_set frame_set) ::
      (* final footprint is disjiont from frame w/o alloc *)
      mk_framecond (mk_eq (mk_inter [alloc_set; frame_wo_alloc]) (mk_empty (Some (Set Loc)))) ::
      (* frame axioms for modified fields *)
      IdSet.fold (fun var frames ->
        let decl = find_global prog var in
        let old_var = oldify var in
        match decl.var_sort with
        | Fld _ as srt -> 
            let frame_axiom = 
              mk_frame 
                init_alloc_set alloc_set 
                frame_set
                (mk_free_const ~srt:srt old_var)
                (mk_free_const ~srt:srt var)
            in 
            mk_framecond frame_axiom :: frames
        | _ -> frames)
        (proc_modifies prog proc) []
    in
    (** update all procedure calls and return commands in body *)
    let rec compile_stmt = function
      | (Call cc, pp) ->
          let assign_alloc =
            let new_alloc_set =
              mk_union [alloc_callee_set; (mk_diff alloc_set init_alloc_callee_set)]
            in
            mk_assign_cmd [alloc_id] [new_alloc_set] pp.pp_pos
          in
          let cc1 = 
            { cc with 
              call_lhs = init_alloc_callee_id :: alloc_callee_id :: cc.call_lhs;
              call_args = alloc_set :: cc.call_args;
            } 
          in
          mk_seq_cmd [Basic (Call cc1, pp); assign_alloc] pp.pp_pos
      | (Return rc, pp) ->
          let rc1 = { return_args = init_alloc_set :: alloc_set :: rc.return_args } in
          Basic (Return rc1, pp)
      | (c, pp) -> Basic (c, pp)
    in
    let body = Util.optmap 
        (fun body ->
          let body1 = map_basic_cmds compile_stmt body in
          let assume_footprint = mk_assume_cmd footprint footprint.spec_pos in
          let assign_alloc = mk_assign_cmd [alloc_id] [init_alloc_set] footprint.spec_pos in
          mk_seq_cmd [assume_footprint; assign_alloc; body1] (prog_point body).pp_pos
        ) proc.proc_body in
    { proc with
      proc_formals = formals;
      proc_returns = returns;
      proc_locals = locals;
      proc_precond = precond :: other_precond;
      proc_postcond = footprint :: postcond :: framecond @ other_postcond;
      proc_body = body;
    } 
  in
  { prog with prog_procs = IdMap.map compile_proc prog.prog_procs }

(** Eliminate all new and dispose commands.
 ** Assumes that alloc sets have been introduced *)
let elim_new_dispose prog =
  let elim = function
    | (New nc, pp) ->
        let havoc = mk_havoc_cmd [nc.new_lhs] pp.pp_pos in
        let arg = mk_free_const ~srt:nc.new_sort nc.new_lhs in
        let aux =
          match nc.new_sort with
          | Loc ->          
              let new_loc = mk_and [mk_not (mk_elem arg alloc_set); mk_neq arg mk_null] in
              let sf = mk_spec_form (FOL new_loc) "new" None pp.pp_pos in
              let assume_fresh = mk_assume_cmd sf pp.pp_pos in
              let assign_alloc = mk_assign_cmd [alloc_id] [mk_union [alloc_set; mk_setenum [arg]]] pp.pp_pos in
              [assume_fresh; assign_alloc]
          | _ -> []
        in
        Seq (havoc :: aux, pp)
    | (Dispose dc, pp) ->
        let arg = dc.dispose_arg in
        let arg_in_alloc = FOL (mk_elem arg alloc_set) in
        let mk_msg callee pos = "Potential double-free." in
        let sf = mk_spec_form arg_in_alloc "check_dispose" (Some mk_msg) pp.pp_pos in
        let check_dispose = mk_assert_cmd sf pp.pp_pos in
        let assign_alloc = mk_assign_cmd [alloc_id] [mk_diff alloc_set (mk_setenum [arg])] pp.pp_pos in
        Seq ([check_dispose; assign_alloc], pp)
    | (c, pp) -> Basic (c, pp)
  in
  let elim_proc proc = { proc with proc_body = Util.optmap (map_basic_cmds elim) proc.proc_body } in
  { prog with prog_procs = IdMap.map elim_proc prog.prog_procs }

(** Eliminate all return commands.
 ** Assumes that all SL formulas have been desugared. *)
let elim_return prog =
  let elim returns mk_postcond_check = function
    | (Return rc, pp) ->
        let rt_assign = 
          mk_assign_cmd returns rc.return_args pp.pp_pos 
        in
        let fls = 
          mk_spec_form (FOL mk_false) "return" None pp.pp_pos 
        in
        let rt_false = mk_assume_cmd fls pp.pp_pos in
        let rt_postcond = mk_postcond_check pp.pp_pos in
        Seq (rt_assign :: rt_postcond @ [rt_false], pp)
    | (c, pp) -> Basic (c, pp)
  in
  let elim_proc proc =
    let mk_postcond_check = 
      let posts = 
        Util.filter_map 
          is_checked_spec
          (fun sf ->
            match sf.spec_form with
            | FOL _ -> sf
            | SL _ -> failwith "elim_return: Found SL formula that should have been desugared.")
          proc.proc_postcond
      in fun pos -> List.map (fun sf -> mk_assert_cmd sf pos) posts
    in
    let body = 
      (** add final check of postcondition at the end of procedure body *)
      let body1 = 
        let return_pos = 
          { sp_file = proc.proc_pos.sp_file;
            sp_start_line = proc.proc_pos.sp_end_line;
            sp_start_col = proc.proc_pos.sp_end_col;
            sp_end_line = proc.proc_pos.sp_end_line;
            sp_end_col = proc.proc_pos.sp_end_col;
          } 
        in
        Util.optmap 
          (fun body -> 
            mk_seq_cmd (body :: mk_postcond_check return_pos) (prog_point body).pp_pos) 
          proc.proc_body
      in
      Util.optmap (map_basic_cmds (elim proc.proc_returns mk_postcond_check)) body1
         
    in
    { proc with proc_body = body }
  in
  { prog with prog_procs = IdMap.map elim_proc prog.prog_procs }

(** Eliminate all procedure calls.
 ** Assumes that SL formulas have been desugared *)
let elim_proc_calls prog = 
  let elim = function
    | (Call cc, pp) ->
        let callee_decl = find_proc prog cc.call_name in
        let subst_pre = List.fold_left2 
            (fun sm id arg -> IdMap.add id arg sm) 
            IdMap.empty callee_decl.proc_formals cc.call_args
        in
        let assert_precond =
          Util.filter_map is_checked_spec 
            (fun sf -> mk_assert_cmd (subst_spec subst_pre sf) pp.pp_pos)
            callee_decl.proc_precond
        in
        let havoc_mods =
          let mods = IdSet.elements (proc_modifies prog callee_decl) in
          mk_havoc_cmd (cc.call_lhs @ mods) pp.pp_pos
        in
        let subst_post = List.fold_left2
            (fun sm id rtn_id -> IdMap.add id rtn_id sm)
            IdMap.empty callee_decl.proc_returns cc.call_lhs
        in
        let assume_postcond =
           Util.filter_map is_free_spec 
            (fun sf -> 
              let sf1 = subst_id_spec subst_post (subst_spec subst_pre sf) in
              mk_assume_cmd sf1 pp.pp_pos)
            callee_decl.proc_postcond
        in
        Seq (assert_precond @ [havoc_mods] @ assume_postcond, pp)
    | (c, pp) -> Basic (c, pp)
  in
  let elim_proc proc = 
    { proc with proc_body = Util.optmap (map_basic_cmds elim) proc.proc_body }
  in
  { prog with prog_procs = IdMap.map elim_proc prog.prog_procs }

(** Eliminate assignment and havoc commands (via SSA computation) 
 ** Assumes that:
 ** - all SL formulas have been desugared
 ** - all loops have been eliminated 
 ** - the only remaining basic commands are assume/assert/assign/havoc. *)
let elim_assign_havoc prog =
  let elim_proc proc =
    let fresh_decl id pos =
      let decl = find_var prog proc id in
      let id1 = fresh_ident (name id) in
      let decl1 = 
        { decl with 
          var_name = id1;
          var_is_aux = true;
          var_pos = pos;
        }
      in decl1
    in
    let fresh sm locals pos ids =
      List.fold_left (fun (sm, locals) id ->
        let decl = fresh_decl id pos in
        IdMap.add id decl.var_name sm, 
        IdMap.add decl.var_name decl locals)
        (sm, locals) ids
    in
    let rec elim sm locals = function
      | Loop _ as c -> sm, locals, c
      | Seq (cs, pp) ->
          let sm, locals, cs1 = 
            List.fold_left 
              (fun (sm, locals, cs1) c  ->
                let sm, locals, c1 = elim sm locals c in
                sm, locals, c1 :: cs1)
              (sm, locals, []) cs
          in
          sm, locals, Seq (List.rev cs1, pp)
      | Choice (cs, pp) ->
          let sms, locals, cs1 =
            List.fold_right  
              (fun c (sms, locals, cs1) ->
                let sm1, locals, c1 = elim sm locals c in
                sm1 :: sms, locals, c1 :: cs1)
              cs ([], locals, [])
          in
          let sm_join = 
            List.fold_left 
              (fun sm1 sm -> 
                IdMap.merge 
                  (fun x -> function 
                    | None -> (function 
                        | None -> None
                        | Some z -> Some z)
                    | Some y -> (function
                        | None -> Some y
                        | Some z -> Some y)
                  )
                  sm1 sm
              )
              IdMap.empty sms
          in
          let cs2 =
            List.fold_right2 (fun sm_c c cs2 ->
              let pp = prog_point c in
              let eqs = 
                IdSet.fold 
                  (fun x eqs ->
                    let x_join = IdMap.find x sm_join in
                    let x_c = IdMap.find x sm_c in
                    if x_join  = x_c then eqs
                    else 
                      let x_decl = find_var prog proc x in
                      let x_srt = x_decl.var_sort in
                      let xc = mk_free_const ~srt:x_srt x_c in
                      let xj = mk_free_const ~srt:x_srt x_join in
                      mk_eq xj xc :: eqs
                  )
                  pp.pp_modifies []
              in 
              let sf = mk_spec_form (FOL (mk_and eqs)) "join" None pp.pp_pos in
              Seq ([c; mk_assume_cmd sf pp.pp_pos], pp) :: cs2)
              sms cs1 []
          in
          sm_join, locals, Choice (cs2, pp)
      | Basic (bc, pp) ->
          match bc with
          | Assume sf -> 
              sm, locals, Basic (Assume (subst_id_spec sm sf), pp)
          | Assert sf ->
              sm, locals, Basic (Assert (subst_id_spec sm sf), pp)
          | Havoc hc ->
              let sm1, locals = fresh sm locals pp.pp_pos hc.havoc_args in
              sm1, locals, Seq ([], pp)
          | Assign ac ->
              let sm1, locals = fresh sm locals pp.pp_pos ac.assign_lhs in
              let eqs =
                List.map2 
                  (fun x e ->
                    let x_decl = find_var prog proc x in
                    let x1 = mk_free_const ~srt:x_decl.var_sort (IdMap.find x sm1) in
                    let e1 = subst_id_term sm e in
                    mk_eq x1 e1)
                  ac.assign_lhs ac.assign_rhs
              in
              let sf = mk_spec_form  (FOL (mk_and eqs)) "assign" None pp.pp_pos in
              sm1, locals, mk_assume_cmd sf pp.pp_pos
          | _ -> sm, locals, Basic (bc, pp)
    in
    let locals, body =
      match proc.proc_body with
      | None -> proc.proc_locals, None
      | Some body -> 
          let _, locals, body1 = elim IdMap.empty proc.proc_locals body in
          locals, Some body1
    in
    { proc with proc_locals = locals; proc_body = body }
  in
  { prog with prog_procs = IdMap.map elim_proc prog.prog_procs }

let vcgen prog =
  let vcp acc proc =
    let rec vcs acc pre = function
      | Loop _ -> 
          failwith "vcgen: loop should have been desugared"
      | Choice (cs, pp) ->
          let acc1, traces = 
            List.fold_left (fun (acc, traces) c ->
              let acc1, trace = vcs acc pre c in
              acc1, trace :: traces)
              (acc, []) cs
          in acc1, [mk_or (List.rev_map mk_and traces)]
      | Seq (cs, pp) -> 
          let acc1, trace, _ = 
            List.fold_right (fun c (acc, trace, pre) ->
              let acc1, c_trace = vcs acc pre c in
              acc1, trace @ c_trace, pre @ c_trace)
              cs (acc, [], pre)
          in
          acc1, trace
      | Basic (bc, pp) ->
          match bc with
          | Assume s ->
              let name = 
                Printf.sprintf "%s_%d_%d" 
                  s.spec_name s.spec_pos.sp_start_line s.spec_pos.sp_start_col
              in
              (match s.spec_form with
              | FOL f -> acc, [mk_comment name f]
              | _ -> failwith "vcgen: found SL formula that should have been desugared")
          | Assert s ->
              let name = 
                Printf.sprintf "%s_%d_%d" 
                  s.spec_name s.spec_pos.sp_start_line s.spec_pos.sp_start_col
              in
              let f =
                match s.spec_form_negated, s.spec_form with
                | Some f, _ -> unoldify_form f
                | None, FOL f -> unoldify_form (mk_not f)
                | _ -> failwith "vcgen: found SL formula that should have been desugared"
              in
              let vc_name = str_of_ident proc.proc_name ^ "_" ^ name in
              let vc_msg = 
                match s.spec_msg with
                | None -> "Assertion violation."
                | Some msg -> msg proc.proc_name s.spec_pos
              in
              let vc = pre @ [mk_comment name f] in
              (vc_name, vc_msg, vc) :: acc, []
          | _ -> 
              failwith "vcgen: found unexpected basic command that should have been desugared"
    in
    match proc.proc_body with
    | Some body -> fst (vcs acc [] body)
    | None -> acc
  in
  IdMap.fold (fun _ proc acc -> vcp acc proc) prog.prog_procs

let simplify prog =
  let prog1 = annotate_modifies prog in
  let prog2 = elim_sl prog1 in
  let prog3 = elim_proc_calls prog2 in
  let prog4 = elim_return prog3 in
  let prog5 = annotate_modifies prog4 in
  let prog6 = elim_assign_havoc prog5 in
  prog6
