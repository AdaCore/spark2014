Require Export checks.
Require Export language_flagged.
Require Export semantics.

Import STACK.

(** * Do Flagged Checks *)
(** do run time checks according to the check flags  *)

Inductive do_flagged_check_on_binop: check_flag -> binary_operator -> value -> value -> check_status -> Prop :=
    | Do_Overflow_Check_Binop: forall op v1 v2,
        do_overflow_check_on_binop op v1 v2 Success ->
        do_flagged_check_on_binop Do_Overflow_Check op v1 v2 Success
    | Do_Overflow_Check_Binop_E: forall op v1 v2,
        do_overflow_check_on_binop op v1 v2 (Exception RTE_Overflow) ->
        do_flagged_check_on_binop Do_Overflow_Check op v1 v2 (Exception RTE_Overflow)
    | Do_Division_By_Zero_Check_Binop: forall v1 v2,
        do_division_check Divide v1 v2 Success ->
        do_flagged_check_on_binop Do_Division_Check Divide v1 v2 Success
    | Do_Division_By_Zero_Check_Binop_E: forall v1 v2,
        do_division_check Divide v1 v2 (Exception RTE_Division_By_Zero) ->
        do_flagged_check_on_binop Do_Division_Check Divide v1 v2 (Exception RTE_Division_By_Zero).

Inductive do_flagged_check_on_unop: check_flag -> unary_operator -> value -> check_status -> Prop :=
    | Do_Overflow_Check_Unop: forall op v,
        do_overflow_check_on_unop op v Success ->
        do_flagged_check_on_unop Do_Overflow_Check op v Success
    | Do_Overflow_Check_Unop_E: forall op v,
        do_overflow_check_on_unop op v (Exception RTE_Overflow) ->
        do_flagged_check_on_unop Do_Overflow_Check op v (Exception RTE_Overflow).

Inductive do_flagged_checks_on_binop: check_flags -> binary_operator -> value -> value -> check_status -> Prop :=
    | Do_No_Check: forall op v1 v2,
        do_flagged_checks_on_binop nil op v1 v2 Success
    | Do_Checks_True: forall ck op v1 v2 cks,
        do_flagged_check_on_binop ck op v1 v2 Success ->
        do_flagged_checks_on_binop cks op v1 v2 Success ->
        do_flagged_checks_on_binop (ck :: cks) op v1 v2 Success
    | Do_Checks_False_Head: forall ck op v1 v2 msg cks,
        do_flagged_check_on_binop ck op v1 v2 (Exception msg) ->
        do_flagged_checks_on_binop (ck :: cks) op v1 v2 (Exception msg)
    | Do_Checks_False_Tail: forall ck op v1 v2 cks msg,
        do_flagged_check_on_binop ck op v1 v2 Success ->
        do_flagged_checks_on_binop cks op v1 v2 (Exception msg) ->
        do_flagged_checks_on_binop (ck :: cks) op v1 v2 (Exception msg).

Inductive do_flagged_checks_on_unop: check_flags -> unary_operator -> value -> check_status -> Prop :=
    | Do_No_Check_Unop: forall op v,
        do_flagged_checks_on_unop nil op v Success
    | Do_Checks_True_Unop: forall ck op v cks,
        do_flagged_check_on_unop ck op v Success ->
        do_flagged_checks_on_unop cks op v Success ->
        do_flagged_checks_on_unop (ck :: cks) op v Success
    | Do_Checks_False_Head_Unop: forall ck op v msg cks,
        do_flagged_check_on_unop ck op v (Exception msg) ->
        do_flagged_checks_on_unop (ck :: cks) op v (Exception msg)
    | Do_Checks_False_Tail_Unop: forall ck op v cks msg,
        do_flagged_check_on_unop ck op v Success ->
        do_flagged_checks_on_unop cks op v (Exception msg) ->
        do_flagged_checks_on_unop (ck :: cks) op v (Exception msg).


(** * Check Flags Extraction Functions *)

Function name_check_flags (n: name_x): check_flags :=
  match n with
  | E_Identifier_X ast_num x cks => cks
  | E_Indexed_Component_X ast_num x_ast_num x e cks => cks
  | E_Selected_Component_X ast_num x_ast_num x f cks => cks
  end.

Function exp_check_flags (e: expression_x): check_flags :=
  match e with
  | E_Literal_X ast_num l cks => cks
  | E_Name_X ast_num n cks    => name_check_flags n
  | E_Binary_Operation_X ast_num op e1 e2 cks => cks
  | E_Unary_Operation_X ast_num op e cks      => cks
  end.

Function update_name_check_flags (n: name_x) (cks: check_flags): name_x :=
  match n with
  | E_Identifier_X ast_num x cks0 => 
      E_Identifier_X ast_num x cks
  | E_Indexed_Component_X ast_num x_ast_num x e cks0 => 
      E_Indexed_Component_X ast_num x_ast_num x e cks
  | E_Selected_Component_X ast_num x_ast_num x f cks0 =>
      E_Selected_Component_X ast_num x_ast_num x f cks
  end.

Function update_exp_check_flags (e: expression_x) (cks: check_flags): expression_x :=
  match e with
  | E_Literal_X ast_num l cks0 =>
      E_Literal_X ast_num l cks
  | E_Name_X ast_num n0 cks0 =>
      let n := update_name_check_flags n0 cks in
        E_Name_X ast_num n cks0
  | E_Binary_Operation_X ast_num op e1 e2 cks0 =>
      E_Binary_Operation_X ast_num op e1 e2 cks
  | E_Unary_Operation_X ast_num op e cks0 =>
      E_Unary_Operation_X ast_num op e cks
  end.


(** * Relational Semantics *)

(** ** Expression Evaluation Semantics *)
(**
    for binary expression and unary expression, if a run time error 
    is detected in any of its child expressions, then return a run
    time error; for binary expression (e1 op e2), if both e1 and e2 
    are evaluated to some normal value, then run time checks are
    performed according to the checking rules specified for the 
    operator 'op', whenever the check fails (returning false), a run 
    time error is detected and the program is terminated, otherwise, 
    normal binary operation result is returned;
*)

Inductive eval_expr_x: symboltable_x -> stack -> expression_x -> Return value -> Prop :=
    | Eval_E_Literal_X: forall l v st s ast_num,
        eval_literal l = v ->
        eval_expr_x st s (E_Literal_X ast_num l nil) (Normal v)
    | Eval_E_Name_X: forall st s n v ast_num,
        eval_name_x st s n v ->
        eval_expr_x st s (E_Name_X ast_num n nil) v
    | Eval_E_Binary_Operation_RTE_E1_X: forall st s e1 msg ast_num op e2 checkflags,
        eval_expr_x st s e1 (Run_Time_Error msg) ->
        eval_expr_x st s (E_Binary_Operation_X ast_num op e1 e2 checkflags) (Run_Time_Error msg)
    | Eval_E_Binary_Operation_RTE_E2_X: forall st s e1 v1 e2 msg ast_num op checkflags,
        eval_expr_x st s e1 (Normal v1) ->
        eval_expr_x st s e2 (Run_Time_Error msg) ->
        eval_expr_x st s (E_Binary_Operation_X ast_num op e1 e2 checkflags) (Run_Time_Error msg)
    | Eval_E_Binary_Operation_RTE_Bin_X: forall st s e1 v1 e2 v2 checkflags op msg ast_num,
        eval_expr_x st s e1 (Normal v1) ->
        eval_expr_x st s e2 (Normal v2) ->
        do_flagged_checks_on_binop checkflags op v1 v2 (Exception msg) ->
        eval_expr_x st s (E_Binary_Operation_X ast_num op e1 e2 checkflags) (Run_Time_Error msg)
    | Eval_E_Binary_Operation_X: forall st s e1 v1 e2 v2 checkflags op v ast_num,
        eval_expr_x st s e1 (Normal v1) ->
        eval_expr_x st s e2 (Normal v2) ->
        do_flagged_checks_on_binop checkflags op v1 v2 Success ->
        Val.binary_operation op v1 v2 = Some v ->
        eval_expr_x st s (E_Binary_Operation_X ast_num op e1 e2 checkflags) (Normal v)
    | Eval_E_Unary_Operation_RTE_E_X: forall st s e msg ast_num op checkflags,
        eval_expr_x st s e (Run_Time_Error msg) ->
        eval_expr_x st s (E_Unary_Operation_X ast_num op e checkflags) (Run_Time_Error msg)
    | Eval_E_Unary_Operation_RTE_X: forall st s e v checkflags op msg ast_num,
        eval_expr_x st s e (Normal v) ->
        do_flagged_checks_on_unop checkflags op v (Exception msg) ->
        eval_expr_x st s (E_Unary_Operation_X ast_num op e checkflags) (Run_Time_Error msg)
    | Eval_E_Unary_Operation_X: forall st s e v checkflags op v1 ast_num,
        eval_expr_x st s e (Normal v) ->
        do_flagged_checks_on_unop checkflags op v Success ->
        Val.unary_operation op v = Some v1 ->
        eval_expr_x st s (E_Unary_Operation_X ast_num op e checkflags) (Normal v1)

with eval_name_x: symboltable_x -> stack -> name_x -> Return value -> Prop :=
    | Eval_E_Identifier_X: forall x s v st ast_num, 
        fetchG x s = Some v ->
        eval_name_x st s (E_Identifier_X ast_num x nil) (Normal v)
    | Eval_E_Indexed_Component_RTE_X: forall e st s msg ast_num x_ast_num x, 
        ~(List.In Do_Range_Check (exp_check_flags e)) ->
        eval_expr_x st s e (Run_Time_Error msg) ->
        eval_name_x st s (E_Indexed_Component_X ast_num x_ast_num x e nil) (Run_Time_Error msg)
    | Eval_E_Indexed_Component_X: forall e st s i x a v ast_num x_ast_num,
        ~(List.In Do_Range_Check (exp_check_flags e)) ->
        eval_expr_x st s e (Normal (BasicV (Int i))) ->
        fetchG x s = Some (AggregateV (ArrayV a)) ->
        array_select a i = Some v ->
        eval_name_x st s (E_Indexed_Component_X ast_num x_ast_num x e nil) (Normal (BasicV v))
    | Eval_E_Indexed_Component_E_RTE_X: forall e cks1 cks2 st s msg ast_num x_ast_num x,
        exp_check_flags e = cks1 ++ Do_Range_Check :: cks2 ->
        eval_expr_x st s (update_exp_check_flags e (cks1 ++ cks2)) (Run_Time_Error msg) ->
        eval_name_x st s (E_Indexed_Component_X ast_num x_ast_num x e nil) (Run_Time_Error msg)
    | Eval_E_Indexed_Component_Range_RTE_X: forall e cks1 cks2 st s i x_ast_num t l u ast_num x, 
        exp_check_flags e = cks1 ++ Do_Range_Check :: cks2 ->
        eval_expr_x st s (update_exp_check_flags e (cks1 ++ cks2)) (Normal (BasicV (Int i))) ->
        fetch_exp_type_x x_ast_num st = Some (Array_Type t) ->
        extract_array_index_range_x st t (Range_X l u) ->
        do_range_check i l u (Exception RTE_Range) ->
        eval_name_x st s (E_Indexed_Component_X ast_num x_ast_num x e nil) (Run_Time_Error RTE_Range)
    | Eval_E_Indexed_Component_Range_X: forall e cks1 cks2 st s i x_ast_num t l u x a v ast_num, 
        exp_check_flags e = cks1 ++ Do_Range_Check :: cks2 ->
        eval_expr_x st s (update_exp_check_flags e (cks1 ++ cks2)) (Normal (BasicV (Int i))) ->
        fetch_exp_type_x x_ast_num st = Some (Array_Type t) ->
        extract_array_index_range_x st t (Range_X l u) ->
        do_range_check i l u Success ->
        fetchG x s = Some (AggregateV (ArrayV a)) ->
        array_select a i = Some v ->
        eval_name_x st s (E_Indexed_Component_X ast_num x_ast_num x e nil) (Normal (BasicV v))
    | Eval_E_Selected_Component_X: forall x s r f v st ast_num x_ast_num,
        fetchG x s = Some (AggregateV (RecordV r)) ->
        record_select r f = Some v ->
        eval_name_x st s (E_Selected_Component_X ast_num x_ast_num x f nil) (Normal (BasicV v)).


(** ** Statement Evaluation Semantics *)

(** *** Copy Out *)
(** Stack manipulation for procedure calls and return *)

Inductive copy_out_x: symboltable_x -> stack -> frame -> list parameter_specification_x -> list expression_x -> Return stack -> Prop :=
    | Copy_Out_Nil_X : forall st s f, 
        copy_out_x st s f nil nil (Normal s)
    | Copy_Out_Cons_Out_X: forall param f v cks s x s' st lparam lexp s'' ast_num x_ast_num,
        param.(parameter_mode_x) = Out \/ param.(parameter_mode_x) = In_Out ->
        fetch param.(parameter_name_x) f = Some v ->
        ~(List.In Do_Range_Check_On_CopyOut cks) ->
        updateG s x v = Some s' ->
        copy_out_x st s' f lparam lexp s'' ->
        copy_out_x st s f (param :: lparam) ((E_Name_X ast_num (E_Identifier_X x_ast_num x cks) nil) :: lexp) s''
    | Copy_Out_Cons_Out_Range_RTE_X: forall param f v cks ast_num st t l u s lparam x_ast_num x lexp,
        param.(parameter_mode_x) = Out \/ param.(parameter_mode_x) = In_Out ->
        fetch param.(parameter_name_x) f = Some (BasicV (Int v)) ->
        List.In Do_Range_Check_On_CopyOut cks ->
        fetch_exp_type_x ast_num st = Some t ->
        extract_subtype_range_x st t (Range_X l u) ->
        do_range_check v l u (Exception RTE_Range) ->
        copy_out_x st s f (param :: lparam) 
                          ((E_Name_X ast_num (E_Identifier_X x_ast_num x cks) nil) :: lexp) 
                          (Run_Time_Error RTE_Range)
    | Copy_Out_Cons_Out_Range_X: forall param f v cks ast_num st t l u s x s' lparam lexp s'' x_ast_num,
        param.(parameter_mode_x) = Out \/ param.(parameter_mode_x) = In_Out ->
        fetch param.(parameter_name_x) f = Some (BasicV (Int v)) ->
        List.In Do_Range_Check_On_CopyOut cks ->
        fetch_exp_type_x ast_num st = Some t ->
        extract_subtype_range_x st t (Range_X l u) ->
        do_range_check v l u Success ->
        updateG s x (BasicV (Int v)) = Some s' ->
        copy_out_x st s' f lparam lexp s'' ->
        copy_out_x st s f (param :: lparam) 
                          ((E_Name_X ast_num (E_Identifier_X x_ast_num x cks) nil) :: lexp) 
                          s''
    | Copy_Out_Cons_In_X: forall param st s f lparam lexp s' e,
        param.(parameter_mode_x) = In ->
        copy_out_x st s f lparam lexp s' ->
        copy_out_x st s f (param :: lparam) (e :: lexp) s'.

(** *** Copy In *)
Inductive copy_in_x: symboltable_x -> stack -> frame -> list parameter_specification_x -> list expression_x -> Return frame -> Prop :=
    | Copy_In_Nil_X : forall st s f, 
        copy_in_x st s f nil nil (Normal f)
    | Copy_In_Cons_In_RTE_X: forall param e st s msg f lparam le,
        param.(parameter_mode_x) = In -> 
        ~(List.In Do_Range_Check (exp_check_flags e)) ->
        eval_expr_x st s e (Run_Time_Error msg) ->
        copy_in_x st s f (param :: lparam) (e :: le) (Run_Time_Error msg)
    | Copy_In_Cons_In_X: forall param e st s v f f' lparam le f'',
        param.(parameter_mode_x) = In -> 
        ~(List.In Do_Range_Check (exp_check_flags e)) ->
        eval_expr_x st s e (Normal v) ->
        push f param.(parameter_name_x) v = f' ->
        copy_in_x st s f' lparam le f'' ->
        copy_in_x st s f (param :: lparam) (e :: le) f''
    | Copy_In_Cons_In_E_RTE_X: forall param e cks1 cks2 st s msg f lparam le,
        param.(parameter_mode_x) = In -> 
        exp_check_flags e = cks1 ++ Do_Range_Check :: cks2 ->
        eval_expr_x st s (update_exp_check_flags e (cks1 ++ cks2)) (Run_Time_Error msg) ->
        copy_in_x st s f (param :: lparam) (e :: le) (Run_Time_Error msg)
    | Copy_In_Cons_In_Range_RTE_X: forall param e cks1 cks2 st s v l u f lparam le,
        param.(parameter_mode_x) = In ->
        exp_check_flags e = cks1 ++ Do_Range_Check :: cks2 ->
        eval_expr_x st s (update_exp_check_flags e (cks1 ++ cks2)) (Normal (BasicV (Int v))) ->
        extract_subtype_range_x st (param.(parameter_subtype_mark_x)) (Range_X l u) ->
        do_range_check v l u (Exception RTE_Range) ->
        copy_in_x st s f (param :: lparam) (e :: le) (Run_Time_Error RTE_Range)
    | Copy_In_Cons_In_Range_X: forall param e cks1 cks2 st s v l u f f' lparam le f'',
        param.(parameter_mode_x) = In -> 
        exp_check_flags e = cks1 ++ Do_Range_Check :: cks2 ->
        eval_expr_x st s (update_exp_check_flags e (cks1 ++ cks2)) (Normal (BasicV (Int v))) ->
        extract_subtype_range_x st (param.(parameter_subtype_mark_x)) (Range_X l u) ->
        do_range_check v l u Success ->
        push f param.(parameter_name_x) (BasicV (Int v)) = f' ->
        copy_in_x st s f' lparam le f'' ->        
        copy_in_x st s f (param :: lparam) (e :: le) f''
    | Copy_In_Cons_Out_X: forall param f f' st s lparam le f'' ast_num x_ast_num x cks,
        param.(parameter_mode_x) = Out ->
        push f param.(parameter_name_x) Undefined = f' ->
        copy_in_x st s f' lparam le f'' ->
        copy_in_x st s f (param::lparam) ((E_Name_X ast_num (E_Identifier_X x_ast_num x cks) nil) :: le) f''
    | Copy_In_Cons_InOut_X: forall param cks x s v f f' st lparam le f'' ast_num x_ast_num,
        param.(parameter_mode_x) = In_Out ->
        ~(List.In Do_Range_Check cks) ->
        fetchG x s = Some v ->
        push f param.(parameter_name_x) v = f' ->
        copy_in_x st s f' lparam le f'' ->
        copy_in_x st s f (param::lparam) ((E_Name_X ast_num (E_Identifier_X x_ast_num x cks) nil) :: le) f''
    | Copy_In_Cons_InOut_Range_RTE_X: forall param cks x s v st l u f lparam le ast_num x_ast_num,
        param.(parameter_mode_x) = In_Out ->
        List.In Do_Range_Check cks ->
        fetchG x s = Some (BasicV (Int v)) ->
        extract_subtype_range_x st (param.(parameter_subtype_mark_x)) (Range_X l u) ->
        do_range_check v l u (Exception RTE_Range) ->
        copy_in_x st s f (param::lparam) ((E_Name_X ast_num (E_Identifier_X x_ast_num x cks) nil) :: le) (Run_Time_Error RTE_Range)
    | Copy_In_Cons_InOut_Range_X: forall param cks x s v st l u f f' lparam le f'' ast_num x_ast_num,
        param.(parameter_mode_x) = In_Out ->
        List.In Do_Range_Check cks ->
        fetchG x s = Some (BasicV (Int v)) ->
        extract_subtype_range_x st (param.(parameter_subtype_mark_x)) (Range_X l u) ->
        do_range_check v l u Success ->
        push f param.(parameter_name_x) (BasicV (Int v)) = f' ->
        copy_in_x st s f' lparam le f'' ->
        copy_in_x st s f (param::lparam) ((E_Name_X ast_num (E_Identifier_X x_ast_num x cks) nil) :: le) f''.



(** Inductive semantic of declarations. [eval_decl s nil decl
    rsto] means that rsto is the frame to be pushed on s after
    evaluating decl, sto is used as an accumulator for building
    the frame.
 *)

(** ** Declaration Evaluation Semantics *)
Inductive eval_decl_x: symboltable_x -> stack -> frame -> declaration_x -> Return frame -> Prop :=
    | Eval_Decl_Null_X: forall st s f,
        eval_decl_x st s f D_Null_Declaration_X (Normal f)
    | Eval_Decl_Type_X: forall st s f ast_num t,
        eval_decl_x st s f (D_Type_Declaration_X ast_num t) (Normal f)
    | Eval_Decl_Var_None_X: forall d st s f ast_num,
        d.(initialization_expression_x) = None ->
        eval_decl_x st s f (D_Object_Declaration_X ast_num d) (Normal (push f d.(object_name_x) Undefined))
    | Eval_Decl_Var_RTE_X: forall d e st f s msg ast_num,
        d.(initialization_expression_x) = Some e ->
        ~(List.In Do_Range_Check (exp_check_flags e)) ->
        eval_expr_x st (f :: s) e (Run_Time_Error msg) ->
        eval_decl_x st s f (D_Object_Declaration_X ast_num d) (Run_Time_Error msg)
    | Eval_Decl_Var_X: forall d e st f s v ast_num,
        d.(initialization_expression_x) = Some e ->
        ~(List.In Do_Range_Check (exp_check_flags e)) ->
        eval_expr_x st (f :: s) e (Normal v) ->
        eval_decl_x st s f (D_Object_Declaration_X ast_num d) (Normal (push f d.(object_name_x) v))
    | Eval_Decl_Var_E_RTE_X: forall d e cks1 cks2 st f s msg ast_num,
        d.(initialization_expression_x) = Some e ->
        exp_check_flags e = cks1 ++ Do_Range_Check :: cks2 ->
        eval_expr_x st (f :: s) (update_exp_check_flags e (cks1 ++ cks2)) (Run_Time_Error msg) ->
        eval_decl_x st s f (D_Object_Declaration_X ast_num d) (Run_Time_Error msg)
    | Eval_Decl_Var_Range_RTE_X: forall d e cks1 cks2 st f s v l u ast_num,
        d.(initialization_expression_x) = Some e ->
        exp_check_flags e = cks1 ++ Do_Range_Check :: cks2 ->
        eval_expr_x st (f :: s) (update_exp_check_flags e (cks1 ++ cks2)) (Normal (BasicV (Int v))) ->
        extract_subtype_range_x st (d.(object_nominal_subtype_x)) (Range_X l u) ->
        do_range_check v l u (Exception RTE_Range) ->        
        eval_decl_x st s f (D_Object_Declaration_X ast_num d) (Run_Time_Error RTE_Range)
    | Eval_Decl_Var_Range_X: forall d e cks1 cks2 st f s v l u ast_num,
        d.(initialization_expression_x) = Some e ->
        exp_check_flags e = cks1 ++ Do_Range_Check :: cks2 ->
        eval_expr_x st (f :: s) (update_exp_check_flags e (cks1 ++ cks2)) (Normal (BasicV (Int v))) ->
        extract_subtype_range_x st (d.(object_nominal_subtype_x)) (Range_X l u) ->
        do_range_check v l u Success ->
        eval_decl_x st s f (D_Object_Declaration_X ast_num d) (Normal (push f d.(object_name_x) (BasicV (Int v))))
    | Eval_Decl_Proc_X: forall st s f ast_num p,
        eval_decl_x st s f (D_Procedure_Body_X ast_num p) (Normal f)
    | Eval_Decl_Seq_E_X: forall st s f d1 msg ast_num d2,
        eval_decl_x st s f d1 (Run_Time_Error msg) ->
        eval_decl_x st s f (D_Seq_Declaration_X ast_num d1 d2) (Run_Time_Error msg)
    | Eval_Decl_Seq_X: forall st s f d1 f' d2 f'' ast_num,
        eval_decl_x st s f d1 (Normal f') ->
        eval_decl_x st s f d2 f'' ->
        eval_decl_x st s f (D_Seq_Declaration_X ast_num d1 d2) f''.

(** Inductive semantic of statement and declaration

   in a statement evaluation, whenever a run time error is detected in
   the evaluation of its sub-statements or sub-component, the
   evaluation is terminated and return a run time error; otherwise,
   evaluate the statement into a normal state.

 *)

Inductive eval_stmt_x: symboltable_x -> stack -> statement_x -> Return stack -> Prop := 
    | Eval_S_Null_X: forall st s,
        eval_stmt_x st s S_Null_X (Normal s)
    | Eval_S_Assignment_RTE_X: forall e st s msg ast_num x,
        ~(List.In Do_Range_Check (exp_check_flags e)) ->
        eval_expr_x st s e (Run_Time_Error msg) ->
        eval_stmt_x st s (S_Assignment_X ast_num x e) (Run_Time_Error msg)
    | Eval_S_Assignment_X: forall e st s v x s1 ast_num,
        ~(List.In Do_Range_Check (exp_check_flags e)) ->
        eval_expr_x st s e (Normal v) ->
        storeUpdate_x st s x v s1 ->
        eval_stmt_x st s (S_Assignment_X ast_num x e) s1
    | Eval_S_Assignment_E_RTE_X: forall e cks1 cks2 st s msg ast_num x,
        exp_check_flags e = cks1 ++ Do_Range_Check :: cks2 ->
        eval_expr_x st s (update_exp_check_flags e (cks1 ++ cks2)) (Run_Time_Error msg) ->
        eval_stmt_x st s (S_Assignment_X ast_num x e) (Run_Time_Error msg)
    | Eval_S_Assignment_Range_RTE_X: forall e cks1 cks2 st s v x t l u ast_num,
        exp_check_flags e = cks1 ++ Do_Range_Check :: cks2 ->
        eval_expr_x st s (update_exp_check_flags e (cks1 ++ cks2)) (Normal (BasicV (Int v))) ->
        fetch_exp_type_x (name_astnum_x x) st = Some t ->
        extract_subtype_range_x st t (Range_X l u) ->
        do_range_check v l u (Exception RTE_Range) ->
        eval_stmt_x st s (S_Assignment_X ast_num x e) (Run_Time_Error RTE_Range)
    | Eval_S_Assignment_Range_X: forall e cks1 cks2 st s v x t l u s1 ast_num,
        exp_check_flags e = cks1 ++ Do_Range_Check :: cks2 ->
        eval_expr_x st s (update_exp_check_flags e (cks1 ++ cks2)) (Normal (BasicV (Int v))) ->
        fetch_exp_type_x (name_astnum_x x) st = Some t ->
        extract_subtype_range_x st t (Range_X l u) ->
        do_range_check v l u Success ->
        storeUpdate_x st s x (BasicV (Int v)) s1 ->
        eval_stmt_x st s (S_Assignment_X ast_num x e) s1
    | Eval_S_If_RTE_X: forall st s b msg ast_num c1 c2,
        eval_expr_x st s b (Run_Time_Error msg) ->
        eval_stmt_x st s (S_If_X ast_num b c1 c2) (Run_Time_Error msg)
    | Eval_S_If_True_X: forall st s b c1 s1 ast_num c2,
        eval_expr_x st s b (Normal (BasicV (Bool true))) ->
        eval_stmt_x st s c1 s1 ->
        eval_stmt_x st s (S_If_X ast_num b c1 c2) s1
    | Eval_S_If_False_X: forall st s b c2 s1 ast_num c1,
        eval_expr_x st s b (Normal (BasicV (Bool false))) ->
        eval_stmt_x st s c2 s1 ->
        eval_stmt_x st s (S_If_X ast_num b c1 c2) s1
    | Eval_S_While_Loop_RTE_X: forall st s b msg ast_num c,
        eval_expr_x st s b (Run_Time_Error msg) ->
        eval_stmt_x st s (S_While_Loop_X ast_num b c) (Run_Time_Error msg)
    | Eval_S_While_Loop_True_RTE_X: forall st s b c msg ast_num,
        eval_expr_x st s b (Normal (BasicV (Bool true))) ->
        eval_stmt_x st s c (Run_Time_Error msg) ->
        eval_stmt_x st s (S_While_Loop_X ast_num b c) (Run_Time_Error msg)
    | Eval_S_While_Loop_True_X: forall st s b c s1 ast_num s2,
        eval_expr_x st s b (Normal (BasicV (Bool true))) ->
        eval_stmt_x st s c (Normal s1) ->
        eval_stmt_x st s1 (S_While_Loop_X ast_num b c) s2 ->
        eval_stmt_x st s (S_While_Loop_X ast_num b c) s2
    | Eval_S_While_Loop_False_X: forall st s b ast_num c,
        eval_expr_x st s b (Normal (BasicV (Bool false))) ->
        eval_stmt_x st s (S_While_Loop_X ast_num b c) (Normal s)
    | Eval_S_Proc_RTE_Args_X: forall p st n pb s args msg ast_num p_ast_num,
        fetch_proc_x p st = Some (n, pb) ->
        copy_in_x st s (newFrame n) (procedure_parameter_profile_x pb) args (Run_Time_Error msg) ->
        eval_stmt_x st s (S_Procedure_Call_X ast_num p_ast_num p args) (Run_Time_Error msg)
    | Eval_S_Proc_RTE_Decl_X: forall p st n pb s args f intact_s s1 msg ast_num p_ast_num,
        fetch_proc_x p st = Some (n, pb) ->
        copy_in_x st s (newFrame n) (procedure_parameter_profile_x pb) args (Normal f) ->
        cut_until s n intact_s s1 -> (* s = intact_s ++ s1 *)
        eval_decl_x st s1 f (procedure_declarative_part_x pb) (Run_Time_Error msg) ->
        eval_stmt_x st s (S_Procedure_Call_X ast_num p_ast_num p args) (Run_Time_Error msg)
    | Eval_S_Proc_RTE_Body_X: forall p st n pb s args f intact_s s1 f1 msg ast_num p_ast_num,
        fetch_proc_x p st = Some (n, pb) ->
        copy_in_x st s (newFrame n) (procedure_parameter_profile_x pb) args (Normal f) ->
        cut_until s n intact_s s1 -> (* s = intact_s ++ s1 *)
        eval_decl_x st s1 f (procedure_declarative_part_x pb) (Normal f1) ->
        eval_stmt_x st (f1 :: s1) (procedure_statements_x pb) (Run_Time_Error msg) ->
        eval_stmt_x st s (S_Procedure_Call_X ast_num p_ast_num p args) (Run_Time_Error msg)
    | Eval_S_Proc_X: forall p st n pb s args f intact_s s1 f1 s2 locals_section params_section s3 s4 ast_num p_ast_num,
        fetch_proc_x p st = Some (n, pb) ->
        copy_in_x st s (newFrame n) (procedure_parameter_profile_x pb) args (Normal f) ->
        cut_until s n intact_s s1 -> (* s = intact_s ++ s1 *)
        eval_decl_x st s1 f (procedure_declarative_part_x pb) (Normal f1) ->          
        eval_stmt_x st (f1 :: s1) (procedure_statements_x pb) (Normal s2) ->
        s2 = (n, locals_section ++ params_section) :: s3 -> (* extract parameters from local frame *)
        length (store_of f) = length params_section ->
        copy_out_x st (intact_s ++ s3) (n, params_section) (procedure_parameter_profile_x pb) args s4 ->
        eval_stmt_x st s (S_Procedure_Call_X ast_num p_ast_num p args) s4
    | Eval_S_Sequence_RTE_X: forall st s c1 msg ast_num c2,
        eval_stmt_x st s c1 (Run_Time_Error msg) ->
        eval_stmt_x st s (S_Sequence_X ast_num c1 c2) (Run_Time_Error msg)
    | Eval_S_Sequence_X: forall st s c1 s1 c2 s2 ast_num,
        eval_stmt_x st s c1 (Normal s1) ->
        eval_stmt_x st s1 c2 s2 ->
        eval_stmt_x st s (S_Sequence_X ast_num c1 c2) s2

with storeUpdate_x: symboltable_x -> stack -> name_x -> value -> Return stack -> Prop := 
    | SU_Identifier_X: forall s x v s1 st ast_num,
        updateG s x v = Some s1 ->
        storeUpdate_x st s (E_Identifier_X ast_num x nil) v (Normal s1)
    | SU_Indexed_Component_RTE_X: forall e st s msg ast_num x_ast_num x v,
        ~(List.In Do_Range_Check (exp_check_flags e)) ->
        eval_expr_x st s e (Run_Time_Error msg) ->
        storeUpdate_x st s (E_Indexed_Component_X ast_num x_ast_num x e nil) v (Run_Time_Error msg)
    | SU_Indexed_Component_Undef_X: forall e st s i x v s1 ast_num x_ast_num,
        ~(List.In Do_Range_Check (exp_check_flags e)) ->
        eval_expr_x st s e (Normal (BasicV (Int i))) ->
        fetchG x s = Some Undefined ->
        updateG s x (AggregateV (ArrayV ((i, v) :: nil))) = Some s1 -> (* a[i] := v *)
        storeUpdate_x st s (E_Indexed_Component_X ast_num x_ast_num x e nil) (BasicV v) (Normal s1)
    | SU_Indexed_Component_X: forall e st s i x a v a1 s1 ast_num x_ast_num,
        ~(List.In Do_Range_Check (exp_check_flags e)) ->
        eval_expr_x st s e (Normal (BasicV (Int i))) ->
        fetchG x s = Some (AggregateV (ArrayV a)) ->
        arrayUpdate a i v = a1 -> (* a[i] := v *)
        updateG s x (AggregateV (ArrayV a1)) = Some s1 ->
        storeUpdate_x st s (E_Indexed_Component_X ast_num x_ast_num x e nil) (BasicV v) (Normal s1)
    | SU_Indexed_Component_E_RTE_X: forall e cks1 cks2 st s msg ast_num x_ast_num x v,
        exp_check_flags e = cks1 ++ Do_Range_Check :: cks2 ->
        eval_expr_x st s (update_exp_check_flags e (cks1 ++ cks2)) (Run_Time_Error msg) ->
        storeUpdate_x st s (E_Indexed_Component_X ast_num x_ast_num x e nil) v (Run_Time_Error msg)
    | SU_Indexed_Component_Range_RTE_X: forall e cks1 cks2 st s i x_ast_num t l u ast_num x v,
        exp_check_flags e = cks1 ++ Do_Range_Check :: cks2 ->
        eval_expr_x st s (update_exp_check_flags e (cks1 ++ cks2)) (Normal (BasicV (Int i))) ->
        fetch_exp_type_x x_ast_num st = Some (Array_Type t) ->
        extract_array_index_range_x st t (Range_X l u) ->
        do_range_check i l u (Exception RTE_Range) ->
        storeUpdate_x st s (E_Indexed_Component_X ast_num x_ast_num x e nil) v (Run_Time_Error RTE_Range)
    | SU_Indexed_Component_Range_Undef_X: forall e cks1 cks2 st s i x_ast_num t l u x v s1 ast_num,
        exp_check_flags e = cks1 ++ Do_Range_Check :: cks2 ->
        eval_expr_x st s (update_exp_check_flags e (cks1 ++ cks2)) (Normal (BasicV (Int i))) ->
        fetch_exp_type_x x_ast_num st = Some (Array_Type t) ->
        extract_array_index_range_x st t (Range_X l u) ->
        do_range_check i l u Success ->
        fetchG x s = Some Undefined ->
        updateG s x (AggregateV (ArrayV ((i, v) :: nil))) = Some s1 -> (* a[i] := v *)
        storeUpdate_x st s (E_Indexed_Component_X ast_num x_ast_num x e nil) (BasicV v) (Normal s1)
    | SU_Indexed_Component_Range_X: forall e cks1 cks2 st s i x_ast_num t l u x a v a1 s1 ast_num,
        exp_check_flags e = cks1 ++ Do_Range_Check :: cks2 ->
        eval_expr_x st s (update_exp_check_flags e (cks1 ++ cks2)) (Normal (BasicV (Int i))) ->
        fetch_exp_type_x x_ast_num st = Some (Array_Type t) ->
        extract_array_index_range_x st t (Range_X l u) ->
        do_range_check i l u Success ->
        fetchG x s = Some (AggregateV (ArrayV a)) ->
        arrayUpdate a i v = a1 -> (* a[i] := v *)
        updateG s x (AggregateV (ArrayV a1)) = Some s1 ->
        storeUpdate_x st s (E_Indexed_Component_X ast_num x_ast_num x e nil) (BasicV v) (Normal s1)
    | SU_Selected_Component_Undef_X: forall r s f v s1 st ast_num r_ast_num,
        fetchG r s = Some Undefined ->
        updateG s r (AggregateV (RecordV ((f, v) :: nil))) = Some s1 -> 
        storeUpdate_x st s (E_Selected_Component_X ast_num r_ast_num r f nil) (BasicV v) (Normal s1)
    | SU_Selected_Component_X: forall r s r1 f v r2 s1 st ast_num r_ast_num,
        fetchG r s = Some (AggregateV (RecordV r1)) ->
        recordUpdate r1 f v = r2 -> (* r1.f := v *)
        updateG s r (AggregateV (RecordV r2)) = Some s1 ->
        storeUpdate_x st s (E_Selected_Component_X ast_num r_ast_num r f nil) (BasicV v) (Normal s1).













