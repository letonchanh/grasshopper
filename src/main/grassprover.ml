open Form
open Axioms
open Util
open Logging

let input_file = ref stdin

let cmd_options =
  [("-v", Arg.Set Debug.verbose, "Display verbose messages");
   ("-noreach", Arg.Clear Config.with_reach_axioms, "Do not add axioms for reachability predicates");
   ("-m", Arg.Set_string Prover.model_file, "Produce model");
   ("-alloc", Arg.Set Config.with_alloc_axioms, "Add axioms for alloc predicate");
   ("-z3q", Arg.Clear Config.instantiate, "Let z3 deal with quantifiers.")
  ]

let usage_message =
  "Usage:\n  " ^ Sys.argv.(0) ^ 
  " [-v] [-noreach] [-nojoin] <input file>\n"

let cmd_line_error msg =
  Arg.usage cmd_options usage_message;
  failwith ("Command line option error: " ^ msg)

(*
let parse_input parse_fct file =
  ParseError.input := Some input_file;
  let lexbuf = Lexing.from_string input in
  ParseError.buffer := Some lexbuf;
  parse_fct lexbuf

let parse_input parse_fct =
  let file = List.hd !input_file in
    parse_given_input parse_fct file
*)

let process_input () =
  (*
  let sl = parse_input (fun lexbuf -> ParseSl.main LexSl.token lexbuf) in
  let _ = Debug.msg ("parsed: " ^ (Sl.to_string sl) ^ "\n") in*)
  let fld = mk_free_const ~srt:(Fld Loc) (fresh_ident "f") in
  let loc1 = mk_free_const ~srt:Loc (fresh_ident "x") in
  let loc2 = mk_free_const ~srt:Loc (fresh_ident "y") in
  let loc3 = mk_free_const ~srt:Loc (fresh_ident "z") in
  let form = mk_reachwo fld loc1 loc2 loc3 in
  let _ = if true || !Debug.verbose then
    print_form stdout form  
  in
  (*print_endline "to prover";*)
  let res = Prover.satisfiable form in
    Printf.fprintf stdout "accumulated time: %.2fs\n" !Util.measured_time;
    match res with
    | Some true -> print_endline "sat"
    | Some false -> print_endline "unsat"
    | None -> print_endline "unknown"

let _ =
  try
    Arg.parse cmd_options (fun s -> input_file := open_in s) usage_message;
    process_input ()
  with  
  | Sys_error s -> output_string stderr (s ^ "\n")
  | Failure s -> output_string stderr (s ^ "\n")
  | Parsing.Parse_error -> output_string stderr "Parse error\n"
	
    
