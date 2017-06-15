{
open SlParser
open Lexing
}

let digit    = ['0'-'9']
let letdig   = ['0'-'9' 'a'-'z' 'A'-'Z' '_' ]
let alphlet  = [        'a'-'z' 'A'-'Z' '_' ]
let ws       = [' ' '\009' '\012']

rule token = parse
    '\r'                { token lexbuf }
  | '\n'                { EOL }

  | "//"[^'\n']*'\n'
                        { token lexbuf }

  | ws                  { token lexbuf }
  | '\"'                { token lexbuf }

  | "Ex."               { EXBINDING }
  | "true"              { TRUE }
  | "emp"               { EMP }
  | "nil"               { NIL }

  | "Prediction"        { PREDICTION }
  | "p="                { PROB_PREFIX }
  | "0."(digit)* as p   { PRED_PROB (p) }

  | "||"                { LOR }
  | "&&"                { LAND }
  | "<>"                { NE }
  | "=="                { EQ }

  | "*"                 { STAR }
  | "->"                { RIGHTARROW }
  | "\\"                { BACKSLASH }
  | "_"                 { NONE }
  | "|"                 { PIPE }

  | ":"                 { COLON }
  | ','                 { COMMA }
  | '.'                 { PERIOD }

  | '('                 { LPAREN }
  | ')'                 { RPAREN }
  | '{'                 { LCURLY }
  | '}'                 { RCURLY }
  | '['                 { LBRACK }
  | ']'                 { RBRACK }

  | (alphlet)(letdig)* as str { ID (str) }
  | eof                 { EOF }
