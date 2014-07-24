Require Export checks_generator.

(** * Check Flags Comparison Function For Program *) 

(** Instead of returning either true or false, it returns unique ast numbers
    denoting where the check flags don't match;
 *)

Module Check_Flags_Comparison_With_Debug_Infor.
  
  Record diff_message: Type := diff {
    ast_number: astnum;
    expected_check_flags: check_flags;
    gnatpro_check_flags : check_flags
  }.

  (** OK: means gnatpro inserted check flags match our formalized check flags
      Mismatch: lists all ast nodes where the check flags are not matching
      Error: means ast trees are not matching, in this case, it is meaningless 
             to compare their check flags
  *)
  Inductive return_message: Type := 
    | OK: return_message
    | Mismatch: list diff_message -> return_message
    | Error.

  (** compare the gnatpro inserted check flags 'cks2' with our formalized check flags 'cks1'; *)
  Function beq_check_flags_msg (ast_num: astnum) (cks1 cks2: check_flags): return_message :=
    if beq_check_flags cks1 cks2 then
      OK
    else
      Mismatch ((diff ast_num cks1 cks2) :: nil).

  Function conj_message (m1 m2: return_message): return_message :=
    match m1 with
    | OK => m2
    | Mismatch diff1 =>
        match m2 with
        | OK => m1
        | Mismatch diff2 => Mismatch (diff1 ++ diff2)
        | Error => Error
        end
     | Error => Error
    end.

  (** ** Check Flags Comparison Function For Expression *)

  Function exp_check_flags_comparison (e1 e2: expression_x): return_message :=
    match e1, e2 with
    | E_Literal_X ast_num l cks, E_Literal_X ast_num' l' cks' =>
        beq_check_flags_msg ast_num cks cks'
    | E_Name_X ast_num n cks, E_Name_X ast_num' n' cks' =>
        conj_message (beq_check_flags_msg ast_num cks cks')
                     (name_check_flags_comparison n n')
    | E_Binary_Operation_X ast_num op e1 e2 cks, E_Binary_Operation_X ast_num' op' e1' e2' cks' =>
        conj_message (beq_check_flags_msg ast_num cks cks')
                     (conj_message (exp_check_flags_comparison e1 e1')
                                   (exp_check_flags_comparison e2 e2'))
     | E_Unary_Operation_X ast_num op e cks, E_Unary_Operation_X ast_num' op' e' cks' =>
        conj_message (beq_check_flags_msg ast_num cks cks')
                     (exp_check_flags_comparison e e')
     | _, _ => Error
     end

  (** ** Check Flags Comparison Function For Name *)

  with name_check_flags_comparison (n1 n2: name_x): return_message :=
    match n1, n2 with
    | E_Identifier_X ast_num x cks, E_Identifier_X ast_num' x' cks' =>
        beq_check_flags_msg ast_num cks cks'
    | E_Indexed_Component_X ast_num x_ast_num x e cks, E_Indexed_Component_X ast_num' x_ast_num' x' e' cks' =>
        conj_message (beq_check_flags_msg ast_num cks cks')
                     (exp_check_flags_comparison e e')
    | E_Selected_Component_X ast_num x_ast_num x f cks, E_Selected_Component_X ast_num' x_ast_num' x' f' cks' =>
        beq_check_flags_msg ast_num cks cks'
    | _, _ => Error
    end.

  Function args_check_flags_comparison (le1 le2: list expression_x): return_message :=
    match le1, le2 with
    | nil, nil => OK
    | (e1 :: le1'), (e2 :: le2') =>
        conj_message (exp_check_flags_comparison e1 e2)
                     (args_check_flags_comparison le1' le2')
    | _, _ => Error
    end.


  (** ** Check Flags Comparison Function For Statement *)

  Function stmt_check_flags_comparison (c1 c2: statement_x): return_message :=
    match c1, c2 with
    | S_Null_X, S_Null_X => OK
    | S_Assignment_X ast_num x e, S_Assignment_X ast_num' x' e' =>
        conj_message (name_check_flags_comparison x x')
                     (exp_check_flags_comparison e e')
    | S_If_X ast_num e c1 c2, S_If_X ast_num' e' c1' c2' =>
        conj_message (exp_check_flags_comparison e e')
                     (conj_message (stmt_check_flags_comparison c1 c1')
                                   (stmt_check_flags_comparison c2 c2'))
    | S_While_Loop_X ast_num e c, S_While_Loop_X ast_num' e' c' =>
        conj_message (exp_check_flags_comparison e e')
                     (stmt_check_flags_comparison c c')
    | S_Procedure_Call_X ast_num p_ast_num p args, S_Procedure_Call_X ast_num' p_ast_num' p' args' =>
        (args_check_flags_comparison args args')
    | S_Sequence_X ast_num c1 c2, S_Sequence_X ast_num' c1' c2' =>
        conj_message (stmt_check_flags_comparison c1 c1')
                     (stmt_check_flags_comparison c2 c2')
    | _, _ => Error
    end.

  Function type_decl_check_flags_comparison (t1 t2: type_declaration_x): return_message :=
    match t1, t2 with
    | Subtype_Declaration_X ast_num tn t (Range_X l u), Subtype_Declaration_X ast_num' tn' t' (Range_X l' u') =>
        OK
    | Derived_Type_Declaration_X ast_num tn t (Range_X l u), Derived_Type_Declaration_X ast_num' tn' t' (Range_X l' u') =>
        OK
    | Integer_Type_Declaration_X ast_num tn (Range_X l u), Integer_Type_Declaration_X ast_num' tn' (Range_X l' u') =>  
        OK
    | Array_Type_Declaration_SubtypeMark_X ast_num tn tm t, Array_Type_Declaration_SubtypeMark_X ast_num' tn' tm' t' =>
        OK
    | Array_Type_Declaration_Range_X ast_num tn (Range_X l u) t, Array_Type_Declaration_Range_X ast_num' tn' (Range_X l' u') t' =>
        OK
    | Record_Type_Declaration_X ast_num tn fs, Record_Type_Declaration_X ast_num' tn' fs' =>
        OK
    | _, _ => 
        Error
    end.

  Function object_decl_check_flags_comparison (o1 o2: object_declaration_x): return_message :=
    match o1, o2 with
    | mkobject_declaration_x ast_num x t None, mkobject_declaration_x ast_num' x' t' None =>
        OK
    | mkobject_declaration_x ast_num x t (Some e), mkobject_declaration_x ast_num' x' t' (Some e') =>
        exp_check_flags_comparison e e'
    | _, _ => 
        Error
    end.

  Function object_decls_check_flags_comparison (lo1 lo2: list object_declaration_x): return_message :=
    match lo1, lo2 with
    | nil, nil => OK
    | o1 :: lo1', o2 :: lo2' => 
        conj_message (object_decl_check_flags_comparison o1 o2)
                     (object_decls_check_flags_comparison lo1' lo2')
    | _, _ => Error
    end.

  Function param_spec_check_flags_comparison (param1 param2: parameter_specification_x): return_message :=
    match param1, param2 with
    | mkparameter_specification_x ast_num x m t, mkparameter_specification_x ast_num' x' m' t' =>
        OK
    end.

  Function param_specs_check_flags_comparison (lparam1 lparam2: list parameter_specification_x): return_message :=
    match lparam1, lparam2 with
    | nil, nil => OK
    | param1 :: lparam1', param2 :: lparam2' => 
        conj_message (param_spec_check_flags_comparison param1 param2)
                     (param_specs_check_flags_comparison lparam1' lparam2')
    | _, _ => Error
    end.

  (** ** Check Flags Comparison Function For Declaration *)

  Function declaration_check_flags_comparison (d1 d2: declaration_x): return_message :=
    match d1, d2 with
    | D_Null_Declaration_X, D_Null_Declaration_X => OK
    | D_Type_Declaration_X ast_num t, D_Type_Declaration_X ast_num' t' => 
        type_decl_check_flags_comparison t t'
    | D_Object_Declaration_X ast_num o, D_Object_Declaration_X ast_num' o' =>
        object_decl_check_flags_comparison o o'
    | D_Procedure_Body_X ast_num p, D_Procedure_Body_X ast_num' p' =>
        procedure_body_check_flags_comparison p p'
    | D_Seq_Declaration_X ast_num d1 d2, D_Seq_Declaration_X ast_num' d1' d2' =>
        conj_message (declaration_check_flags_comparison d1 d1')
                     (declaration_check_flags_comparison d2 d2')
    | _, _ => Error
    end

  with procedure_body_check_flags_comparison (p1 p2: procedure_body_x): return_message :=
    match p1, p2 with
    | mkprocedure_body_x ast_num p params decls stmt, mkprocedure_body_x ast_num' p' params' decls' stmt' =>
        conj_message (param_specs_check_flags_comparison params params')
                     (conj_message (declaration_check_flags_comparison decls decls')
                                   (stmt_check_flags_comparison stmt stmt'))
    end.

End Check_Flags_Comparison_With_Debug_Infor.










