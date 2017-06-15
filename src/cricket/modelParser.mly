%{
  open Lexing
  open State
%}

%token <string> IDENT
%token <int64> NUM
%token COLON COMMA 
%token LPAREN RPAREN LBRACK RBRACK
%token ADDRTYP INTTYP
%token EOF

%start heap
%type <((string * State.valu) list * (int64 * string * State.valu) list)> heap
%%

heap:
    varList fieldList { ($1, $2) }
  | varList { ($1, []) }
  | EOF { ([], [])}

varList:
    varDef { [ $1 ] }
  | varDef varList { $1 :: $2 }

fieldList:
    pointsToDef { [ $1 ] }
  | pointsToDef fieldList { $1 :: $2 }

varDef:
    LBRACK IDENT COLON ADDRTYP NUM RBRACK { ($2, ValAddr $5) }
  | LBRACK IDENT COLON INTTYP NUM RBRACK { ($2, ValInt $5) }

pointsToDef:
    LPAREN NUM COMMA IDENT COMMA ADDRTYP NUM RPAREN { ($2, $4, ValAddr $7) }
  | LPAREN NUM COMMA IDENT COMMA INTTYP NUM RPAREN { ($2, $4, ValInt $7) }
