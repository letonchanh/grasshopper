{
open Programs
open SplParser
open Lexing

(* set file name *)
let set_file_name lexbuf name =
lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = name }


let keyword_table = Hashtbl.create 32
let _ =
  List.iter (fun (kwd, tok) -> Hashtbl.add keyword_table kwd tok)
    ([("assert", ASSERT);
      ("assume", ASSUME);
      ("bool", BOOL);
      ("else", ELSE);
      ("emp", EMP);
      ("ensures", ENSURES);
      ("false", BOOLVAL(false));
      ("free", DISPOSE);
      ("ghost", GHOST);
      ("if", IF);
      ("int", INT);
      ("invariant", INVARIANT);
      ("new", NEW);
      ("null", NULL);
      ("predicate", PREDICATE);
      ("procedure", PROCEDURE);
      ("requires", REQUIRES);
      ("return", RETURN);
      ("returns", RETURNS);
      ("struct", STRUCT);
      ("true", BOOLVAL(true));
      ("var", VAR);
      ("while", WHILE);
   ])
}

let digitchar = ['0'-'9']
let idchar = ['A'-'Z''a'-'z''_']
let ident = idchar (idchar | digitchar)*
let digits = digitchar+

rule token = parse
  [' ' '\t'] { token lexbuf }
| '\n' { Lexing.new_line lexbuf; token lexbuf }
| "//" [^ '\n']* { token lexbuf }
| "==" { EQ }
| "!=" { NEQ }
| "<=" { LEQ }
| ">=" { GEQ }
| "<" { LT }
| ">" { GT }
| "||" { OR }
| "&&" { AND }
| '!' { NOT }
| '+' { PLUS }
| '-' { MINUS }
| '/' { DIV }
| '*' { TIMES }
| '(' { LPAREN }
| ')' { RPAREN }
| '{' { LBRACE }
| '}' { RBRACE }
| ":=" { COLONEQ }
| ':' { COLON }
| ';' { SEMICOLON }
| ',' { COMMA }
| '.' { DOT }
| "&*&" { SEP }
| "|->" { PTS }
| '|' { PIPE }
| ident as kw
    { try
        Hashtbl.find keyword_table kw
      with Not_found ->
        IDENT (kw)
    }
| digits as num { INTVAL (int_of_string num) }
| eof { EOF }
| _ { let pos = lexeme_start_p lexbuf in 
      let spos = 
        { sp_file = pos.pos_fname;
          sp_start_line = pos.pos_lnum;
          sp_start_col = pos.pos_cnum - pos.pos_bol;
          sp_end_line = pos.pos_lnum;
          sp_end_col = pos.pos_cnum - pos.pos_bol;
        } 
      in
      ProgError.lexical_error spos
    }
