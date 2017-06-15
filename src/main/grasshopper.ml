(** Main module of GRASShopper *)

open Util
open SplCompiler
    
let greeting =
  "GRASShopper version " ^ Config.version ^ "\n"
                                              
let usage_message =
  greeting ^
  "\nUsage:\n  " ^ Sys.argv.(0) ^ 
  " <input file> [options]\n"

let cmd_line_error msg =
  Arg.usage (Arg.align Config.cmd_options) usage_message;
  failwith ("Command line option error: " ^ msg)

(** Output JSON file with error trace *)
let output_trace prog proc (pp, model) =
  if !Config.trace_file = "" then () else
  begin
    let trace = Verifier.get_trace prog proc (pp, model) in
    (* print trace to trace file in JSON format *)
    let trace_chan = open_out !Config.trace_file in
    let print_pos (pos, state) =
      Printf.fprintf trace_chan 
        "{\"position\": {\"line_no\": %d, \"column_no_start\": %d, \"column_no_stop\": %d}, \"state\": "
        pos.Grass.sp_start_line pos.Grass.sp_start_col pos.Grass.sp_end_col;
      ModelPrinting.output_json trace_chan state;
      output_string trace_chan "}"
    in
    output_string trace_chan "[";
    Util.output_list trace_chan print_pos ",\n" trace;
    output_string trace_chan "]\n";
    close_out trace_chan     
  end

(** Parse compilation unit in file [file] using parsing function [parse_fct] *)
let parse_cu parse_fct file =
  let input = read_file file in
  ParseError.input := Some input;
  let lexbuf = Lexing.from_string input in
  ParseError.buffer := Some lexbuf;
  SplLexer.set_file_name lexbuf file; 
  parse_fct lexbuf

(** normalize the filenames to avoid double inclusion *)
let normalizeFilename base_dir file_name =
  let fullname =
    if Filename.is_relative file_name then
      base_dir ^ Filename.dir_sep ^ file_name
    else
      file_name
  in
  let sep = Str.regexp_string Filename.dir_sep in
  let parts = Str.split_delim sep fullname in
  let remaining =
    List.fold_left
      (fun acc -> function
        | "" when acc <> [] -> acc
        | ".." -> List.tl acc
        | x -> x :: acc
      )
      []
      parts
  in
  String.concat Filename.dir_sep (List.rev remaining)

(** Parse SPL program in main file [main_file] *)
let parse_spl_program main_file =
  let rec parse parsed to_parse spl_prog =
    match to_parse with
    | (dir, file, pos) :: to_parse1 ->
        if not (StringSet.mem file parsed) then
          begin
            Debug.debug (fun () -> "parsing: " ^ file ^ "\n");
            let cu = 
              try 
                parse_cu (fun lexbuf -> SplParser.main SplLexer.token lexbuf) file 
              with Sys_error _ ->
                ProgError.error pos ("Could not find file " ^ file)
            in
            let parsed1 = StringSet.add file parsed in
            let to_parse2 =
              List.fold_left
                (fun acc (incl, pos) ->
                  let incl2 = normalizeFilename dir incl in
                  let dir2 = Filename.dirname incl2 in
                  (dir2, incl2, pos) :: acc)
                to_parse1
                cu.SplSyntax.includes 
            in
            parse parsed1 to_parse2 (SplSyntax.merge_spl_programs spl_prog cu)
          end
        else
          begin
            Debug.debug (fun () -> "already included: " ^ file ^ "\n");
            parse parsed to_parse1 spl_prog
          end
    | [] -> spl_prog
  in
  let norm_dir = normalizeFilename (Unix.getcwd ()) !Config.base_dir in
  let main_file = normalizeFilename norm_dir main_file in
  let main_dir  =
    if !Config.base_dir <> "" then norm_dir
    else Filename.dirname main_file
  in
  let prog =
    parse
      StringSet.empty
      [(main_dir, main_file, GrassUtil.dummy_position)]
      SplSyntax.empty_spl_program in
  prog

(** Cricket: invariant inference engine *)

(** Gets models for failing VCs at line number [lnum] of [spl_prog] *)
let get_models_for_prog spl_prog proc_name assert_pos =
  Cricket.clear_identifiers ();

  if Cricket.do_log_debug () then
    SplSyntax.print_spl_program stdout spl_prog;

  let spl_prog = SplChecker.check (SplSyntax.add_alloc_decl spl_prog) in
  let prog = SplTranslator.to_program spl_prog in
  let simple_prog = Verifier.simplify prog in

  let proc = Prog.find_proc simple_prog proc_name in
  let robust_val = !Config.robust in
  Config.robust := true;
  let errors = Verifier.check_proc simple_prog proc in
  Config.robust := robust_val;

  let rec find_error = function
    | (err_pos, _, model, model_list) :: errs ->
       (* Printf.fprintf stdout "Found error on line %d\n" err_pos.Grass.sp_start_line; *)
       if err_pos = assert_pos then model :: model_list
       else find_error errs
    | [] -> []    
  in
  find_error errors

(** Given a model and an SL formula, constructs an spl program that checks if the assertion holds for the given model *)
let assert_formula_about_model var_decls formula model_filename =
  let store, heap = Locust.read_heap_from_file model_filename  in

  Cricket.clear_identifiers ();

  (* Include all the data structure definitions *)
  let spl_prog = parse_spl_program "tests/spl/include/cricket_defs.spl" in

  let spl_prog, proc_name =
    Locust.add_model_and_assertion_to_prog var_decls (store, heap) formula spl_prog in

  if Cricket.do_log_spew () then
    SplSyntax.print_spl_program stdout spl_prog;

  try
    (* This part copied from Grasshopper.check_spl_program: *)
    let spl_prog = SplChecker.check (SplSyntax.add_alloc_decl spl_prog) in
    let prog = SplTranslator.to_program spl_prog in
    let simple_prog = Verifier.simplify prog in
    
    let dummy_proc = Prog.find_proc simple_prog proc_name in        
    let errors = Cricket.run_grasshopper (fun () -> Verifier.check_proc simple_prog dummy_proc) in
    match errors with
    | [] -> false
    | _ -> true
  with
  | _ -> false

let beetle file =
  let spl_prog = parse_spl_program file in

  Cricket.log_msg "Executing program to get samples";
  let sampled_sts =
    Sampler.sample get_models_for_prog spl_prog false 10
  in

  Cricket.log_msg "Calling Beetle";
  Beetle.learn_annotations
    assert_formula_about_model
    spl_prog
    sampled_sts;

  Cricket.log (-1)
    (Format.sprintf
      "Program succesfully verified [%.2fs total, %.2fs beetle, %.2fs beetle-grasshopper]."
        (Unix.gettimeofday() -. Cricket.basetime)
        (!Cricket.beetle_time) (!Cricket.grasshopper_time))

let locust file =
  let spl_prog = parse_spl_program file in

  Cricket.log_msg "Executing program to get samples";
  let samples = Sampler.sample get_models_for_prog spl_prog true 6 in

  Locust.infer_invariant assert_formula_about_model spl_prog samples
  |> ignore;

  Cricket.log (-1)
    (Format.sprintf
      "Program succesfully verified [%.2fs total, %.2fs platypus, %.2fs locust-grasshopper]."
        (Unix.gettimeofday() -. Cricket.basetime) (!Cricket.platypus_time)
        (!Cricket.grasshopper_time))

(** Main entry point for cricket *)
let cricket input_file =
  let spl_prog = parse_spl_program input_file in

  let in_frame = Cricket.compute_in_frame_pars spl_prog in
  (* Hashtbl.iter (fun pname vars -> Cricket.log_msg (Printf.sprintf "Proc %s, in-frame vars [%s]" (fst pname) (String.concat ", " (Util.StringSet.elements vars)))) in_frame; *)
  
  Cricket.log_msg "Executing program to get samples for Locust";
  Config.locust := true;
  Config.beetle := false;
  let l_samples = Sampler.sample get_models_for_prog spl_prog true 6 in

  Cricket.log_msg "Calling Locust";
  let learning_state =
    Locust.infer_invariant assert_formula_about_model spl_prog l_samples
  in

  Cricket.log_msg "Inserting learnt invariants into original program";
  let prog_w_shape_invs =
    Locust.insert_annotations_into_spl_prog
      ~main:true ~frame:(Some in_frame) spl_prog learning_state
  in
  (* let out_chan = open_out "_prog.spl" in *)
  (* SplSyntax.print_spl_program out_chan prog_w_shape_invs; *)
  (* close_out out_chan; *)
  (* Cricket.log_msg ("Written annotated SPL program to _prog.spl"); *)

  let locust_grasshopper_time = !Cricket.grasshopper_time in
  Cricket.grasshopper_time := 0.0;
  
  Cricket.log_msg "Executing program to get samples for Beetle";
  Config.locust := false;
  Config.beetle := true;
  let samples = Sampler.sample get_models_for_prog prog_w_shape_invs false 10 in

  Cricket.log_msg "Calling Beetle";
  Beetle.learn_annotations
    assert_formula_about_model
    prog_w_shape_invs
    samples;

  Cricket.log (-1)
    (Format.sprintf
      "Program succesfully verified [%.2fs total, %.2fs platypus, %.2fs locust-grasshopper, %.2fs beetle, %.2fs beetle-grasshopper]."
        (Unix.gettimeofday() -. Cricket.basetime) (!Cricket.platypus_time) locust_grasshopper_time
        (!Cricket.beetle_time) (!Cricket.grasshopper_time))
   
(** Check SPL program in main file [file] and procedure [proc] *)
let check_spl_program spl_prog proc =
  let spl_prog = SplChecker.check (SplSyntax.add_alloc_decl spl_prog) in
  let prog = SplTranslator.to_program spl_prog in
  let simple_prog = Verifier.simplify prog in
  let check simple_prog first proc =
    let errors =
      if !Config.typeonly then []
      else Verifier.check_proc simple_prog proc
    in
    List.fold_left
      (fun first (pp, error_msg, model, _) ->
        output_trace simple_prog proc (pp, model);
        let _ =
          if !Config.robust
          then begin
            (if not first then print_newline ());
            ProgError.print_error pp error_msg
          end
          else ProgError.error pp error_msg
        in
        false
      )
      first errors
  in
  match proc with
  | None -> Prog.fold_procs (check simple_prog) true simple_prog
  | Some p ->
    let procs =
      Prog.find_proc_with_deps simple_prog (p, 0)
    in
    if procs = [] then begin
      let available =
        Prog.fold_procs 
          (fun acc proc ->
            let name = Prog.name_of_proc proc in
            "\t" ^ Grass.string_of_ident name ^ "\n" ^ acc) 
          "" prog
      in
      failwith ("Could not find a procedure named " ^ p ^ 
                ". Available procedures are:\n" ^ available)
    end;
    List.fold_left (check simple_prog) true procs


(** Get current time *)
let current_time () =
  let ptime = Unix.times () in
  ptime.Unix.tms_utime +. ptime.Unix.tms_cutime  

(** Print statistics *)
let print_stats start_time =
  if !Config.print_stats then
    let end_time = current_time () in
    let total_time = end_time -. start_time in
    print_endline "Statistics: ";
    Printf.printf "  running time for analysis: %.2fs\n" total_time;
    Printf.printf "  # VCs: %d\n" !SmtLibSolver.num_of_sat_queries;
    Printf.printf "  measured time: %.2fs\n" !Util.measured_time;
    Printf.printf "  # measured calls: %.2d\n" !Util.measured_calls

(** Print C program equivalent *)
let print_c_program spl_prog =
  if !Config.compile_to <> "" then begin
    let oc = open_out !Config.compile_to in
    SplCompiler.compile oc spl_prog;
    close_out oc;
  end else 
    ()

(** Main entry of GRASShopper *)
let _ =
  let main_file = ref "" in
  let set_main_file s =
    main_file := s;
  in
  let start_time = current_time () in
  try
    Arg.parse Config.cmd_options set_main_file usage_message;
    if !Config.unsat_cores then Config.named_assertions := true;
    Debug.info (fun () -> greeting);
    SmtLibSolver.select_solver (String.uppercase !Config.smtsolver);
    if !main_file = "" then
      cmd_line_error "input file missing"
    else if !Config.cricket then
      cricket !main_file
    else if !Config.locust then
      locust !main_file
    else if !Config.beetle then
      beetle !main_file
    else
      begin
      let spl_prog = parse_spl_program !main_file in
      let res = check_spl_program spl_prog !Config.procedure in
      print_stats start_time; 
      print_c_program spl_prog;
      if !Config.verify && res then
        Debug.info (fun () -> "Program successfully verified.\n")
    end
  with  
  | Sys_error s -> 
      let bs = if Debug.is_debug 0 then Printexc.get_backtrace () else "" in
      output_string stderr ("Error: " ^ s ^ "\n" ^ bs); exit 1
  | Failure s ->
      let bs = if Debug.is_debug 0 then Printexc.get_backtrace () else "" in
      output_string stderr ("Error: " ^ s ^ "\n" ^ bs); exit 1
  | Parsing.Parse_error -> 
      print_endline "parse error"; 
      exit 1
  | ProgError.Prog_error _ as e ->
     Printexc.print_backtrace stderr;
      output_string stderr (ProgError.to_string e ^ "\n");
      exit 1
	

