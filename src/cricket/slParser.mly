%{
  open Grass
  open SplSyntax
  open Lexing

  let mk_position s e =
    let start_pos = Parsing.rhs_start_pos s in
    let end_pos = Parsing.rhs_end_pos e in
    { sp_file = "predictor_output";
      sp_start_line = start_pos.pos_lnum;
      sp_start_col = start_pos.pos_cnum - start_pos.pos_bol;
      sp_end_line = end_pos.pos_lnum;
      sp_end_col = end_pos.pos_cnum - end_pos.pos_bol;
    }

  let find_typ_of_var var =
    match idmap_find_uniq (fst var) !SlParserStateHack.current_parse_vars with
    | Some v -> v.v_type
    | None ->
        let vars_in_scope =
            IdMap.bindings !SlParserStateHack.current_parse_vars
            |> List.map (fun ((id, x), _) -> Printf.sprintf "%s_%d" id x)
            |> String.concat ", "
        in
        failwith @@ Printf.sprintf "Couldn't find variable %s in vars in scope: %s" (fst var) vars_in_scope

%}

%token <string> ID
%token EXBINDING TRUE EMP NIL
%token LSEG BTWN
%token PREDICTION PROB_PREFIX
%token <string> PRED_PROB
%token LOR LAND NE EQ
%token STAR RIGHTARROW BACKSLASH NONE PIPE
%token COLON COMMA PERIOD
%token LPAREN RPAREN LBRACK RBRACK LCURLY RCURLY
%token EOF EOL

%start formula

%type <(float * SplSyntax.expr)> formula

%%

formulae :
    | formula EOL  { [$1] }
    | formula EOL formulae  { $1 :: $3 }

formula :
/*    | EXBINDING varList PERIOD pureFormula COLON spatialFormula
        { SymHeap.ofSeqs $2 $6 $8 (fst $10) (snd $10) } */
    | pred_accuracy COLON disjuncts
        { ($1, $3) }
    ;

disjuncts :
    | pureFormula COLON spatialFormula { BinaryOp ($1, OpSepStar, $3, PermType, mk_position 1 3) }
    | pureFormula COLON spatialFormula LOR disjuncts { BinaryOp (BinaryOp ($1, OpSepStar, $3, PermType, mk_position 1 3), OpOr, $5, PermType, mk_position 4 4) }

pred_accuracy :
    | PREDICTION LCURLY PROB_PREFIX PRED_PROB RCURLY { float_of_string $4 }

var : ID
    {
        let id = ($1, 0) in
        let typ = find_typ_of_var id in
        let decl =
	    {
              v_name = id;
	      v_type = typ;
	      v_ghost = false;
	      v_implicit = false;
	      v_aux = false;
	      v_pos = mk_position 1 1;
	      v_scope = GrassUtil.global_scope; (* TODO scope is fixed later?? *)
	    }
	   in
        decl
    }
    ;

varList :
    | var               { [ $1 ] }
    | var COMMA varList { $1 :: $3 }
    ;

expr :
    | NIL  { Null (AnyRefType, mk_position 1 1) }
    | ID  { Ident (($1, 0), mk_position 1 1) }
    | ID PERIOD ID  { Read (Ident (($3, 0), mk_position 3 3), Ident (($1, 0), mk_position 1 1), mk_position 1 3) }
    ;

exprList :
    | expr                { [ $1 ] }
    | expr COMMA exprList { $1 :: $3 }
    ;

pureFormulaAtom :
    | expr NE expr
      {
        let (left_arg, right_arg) = ($1, $3) in
        match (left_arg, right_arg) with
        | (Ident (left_id, _), Ident (right_id, _)) ->
          let left_typ = find_typ_of_var left_id in
          let right_typ = find_typ_of_var right_id in
          if left_typ <> right_typ then
             BoolVal (true, mk_position 1 3)
          else
             UnaryOp (OpNot, BinaryOp (left_arg, OpEq, right_arg, BoolType, mk_position 1 3), mk_position 1 3)
        | _ -> UnaryOp (OpNot, BinaryOp (left_arg, OpEq, right_arg, BoolType, mk_position 1 3), mk_position 1 3)
      }
    | expr EQ expr
      {
        let (left_arg, right_arg) = ($1, $3) in
        match (left_arg, right_arg) with
        | (Read (Ident (("parent", 0), _), _, _), _) ->
           BoolVal (true, mk_position 1 3)
        | _ ->
           BinaryOp ($1, OpEq, $3, BoolType, mk_position 1 3)
      }
    ;

pureFormula :
    | pureFormulaAtom LAND pureFormula { BinaryOp ($1, OpSepStar, $3, AnyType, mk_position 1 3)}
    | pureFormulaAtom                  { $1 }
    | TRUE                             { BoolVal (true, mk_position 1 1) }
    ;

/*
pointsTo :
    | expr RIGHTARROW LBRACK exprList RBRACK
        { PointsTo ($1, $4) }
*/

predicate :
    | ID LPAREN exprList PIPE NONE RPAREN
        { if $1 = "ls" then
             PredApp (Pred ("lseg", 0), $3, mk_position 1 4)
          else if $1 = "tree" then
             PredApp (Pred ("tree", 0), $3, mk_position 1 4)
          else
             failwith (Printf.sprintf "Unknown predicate type %s." $1)
        }
    /* ls  (    varA, nil   |      \    v5, v6, v7, v8      ->     true   :   ls   (    v7, nil   |    _     )      *  emp    )   */
    /* 1    2      3        4      5          6             7        8    9   10   11      12     13   14   15     16  17    18   */
    | ID LPAREN exprList  PIPE BACKSLASH   exprList     RIGHTARROW TRUE COLON ID LPAREN exprList PIPE NONE RPAREN STAR EMP RPAREN
        {
          let outerPred = $1 in
          let innerPred = $10 in
          let lambdaArgs = $6 in
          let innerArgs = $12 in          
          if outerPred = "ls" then
            let innerStart = List.hd innerArgs in            
            if innerPred = "ls" then
              let valueArg = List.nth lambdaArgs 2 in
              let innerEnd = List.hd (List.tl innerArgs) in
              match (innerStart, innerEnd, valueArg) with
              | (Ident (innerStartId, _), Null _, Ident(valueId, _)) when innerStartId = valueId ->
                 PredApp (Pred ("list_of_lists", 0), $3, mk_position 1 4)
              | (_, Null _, _) ->
                 failwith (Printf.sprintf "Nested predicate parsed, but inner list start %s does not fit expected %s." (SplSyntax.string_of_expr innerStart) (SplSyntax.string_of_expr valueArg))
              | _ ->
                failwith (Printf.sprintf "Structure of nested predicate not understood: Does not end in nil.")
            else if innerPred = "tree" then
              let valueArg = List.nth lambdaArgs 2 in
              match (innerStart, valueArg) with
              | (Ident (innerId, _), Ident(valueId, _)) when innerId = valueId -> 
                 PredApp (Pred ("list_of_trees", 0), $3, mk_position 1 4)
              | _ ->
                 failwith (Printf.sprintf "Nested predicate parsed, but inner tree start %s does not fit expected %s." (SplSyntax.string_of_expr innerStart) (SplSyntax.string_of_expr valueArg))
            else
               failwith (Printf.sprintf "Unknown nested predicate type %s(..., \ ... -> %s(...))." outerPred innerPred)
          else if outerPred = "tree" then
            let innerStart = List.hd innerArgs in            
            if innerPred = "ls" then
              let valueArg = List.nth lambdaArgs 1 in
              let innerEnd = List.hd (List.tl innerArgs) in
              match (innerStart, innerEnd, valueArg) with
              | (Ident (innerStartId, _), Null _, Ident(valueId, _)) when innerStartId = valueId ->
                 PredApp (Pred ("tree_of_lists", 0), $3, mk_position 1 4)
              | (_, Null _, _) ->
                 failwith (Printf.sprintf "Nested predicate parsed, but inner list start %s does not fit expected %s." (SplSyntax.string_of_expr innerStart) (SplSyntax.string_of_expr valueArg))
              | _ ->
                 failwith (Printf.sprintf "Structure of nested predicate not understood: Does not end in nil.")
            else
               failwith (Printf.sprintf "Unknown nested predicate type %s(..., \ ... -> %s(...))." outerPred innerPred)
          else
             failwith (Printf.sprintf "Unknown nested predicate type %s(..., \ ... -> %s(...))." outerPred innerPred)
        }
    | ID LPAREN exprList RPAREN
        {
          if $1 = "btwn" then
             PredApp (BtwnPred, $3, mk_position 1 4)
          else if $1 = "acc" then
             match List.hd $3 with
             | Ident (id, _) ->
               let typ = find_typ_of_var id in
               PredApp (AccessPred, [Setenum(typ, $3, mk_position 1 4)], mk_position 1 4)
             | _ -> failwith (Printf.sprintf "Cannot determine type of variable")
          else
            failwith (Printf.sprintf "Unknown predicate %s" $1)
        }
    ;

spatialFormula :
    | TRUE                                   { BoolVal (true, mk_position 1 1) }
    | predicate STAR spatialFormula          { BinaryOp ($1, OpSepStar, $3, PermType, mk_position 1 3) }
    | predicate                              { $1 }
    | EMP                                    { Emp (mk_position 1 1) }
      /*
    | pointsTo STAR spatialFormula           { (fst $3, $1 :: snd $3) }
    | pointsTo                               { ([], [$1]) } */
    ;
