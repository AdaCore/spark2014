Require Export checks.
Require Export language_flagged.
Require Export semantics.

Import Symbol_Table_Module_X.

Import STACK.

(** * Do Flagged Checks *)
(** do run time checks according to the check flags  *)

Inductive do_flagged_check_on_binop: check_flag -> binary_operator -> value -> value -> check_status -> Prop :=
    | Do_Overflow_Check_Binop: forall op v1 v2,
        do_overflow_check op v1 v2 Success ->
        do_flagged_check_on_binop Do_Overflow_Check op v1 v2 Success
    | Do_Overflow_Check_Binop_E: forall op v1 v2,
        do_overflow_check op v1 v2 (Exception RTE_Overflow) ->
        do_flagged_check_on_binop Do_Overflow_Check op v1 v2 (Exception RTE_Overflow)
    | Do_Division_By_Zero_Check_Binop: forall v1 v2,
        do_division_check Divide v1 v2 Success ->
        do_flagged_check_on_binop Do_Division_Check Divide v1 v2 Success
    | Do_Division_By_Zero_Check_Binop_E: forall v1 v2,
        do_division_check Divide v1 v2 (Exception RTE_Overflow) ->
        do_flagged_check_on_binop Do_Division_Check Divide v1 v2 (Exception RTE_Overflow).

Inductive do_flagged_check_on_unop: check_flag -> unary_operator -> value -> check_status -> Prop :=
    | Do_Overflow_Check_Unop: forall op v,
        do_overflow_check_on_unop op v Success ->
        do_flagged_check_on_unop Do_Overflow_Check op v Success
    | Do_Overflow_Check_Unop_E: forall op v,
        do_overflow_check_on_unop op v (Exception RTE_Overflow) ->
        do_flagged_check_on_unop Do_Overflow_Check op v (Exception RTE_Overflow).

Inductive do_flagged_index_check: check_flag -> Z -> Z -> Z -> check_status -> Prop :=
    | Do_Index_Check_Array: forall i l u,
        do_index_check i l u Success ->
        do_flagged_index_check Do_Index_Check i l u Success
    | Do_Index_Check_Array_E: forall i l u,
        do_index_check i l u (Exception RTE_Overflow) ->
        do_flagged_index_check Do_Index_Check i l u (Exception RTE_Index).


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

Inductive do_flagged_index_checks: check_flags -> Z -> Z -> Z -> check_status -> Prop :=
    | Do_No_Check_Index: forall i l u,
        do_flagged_index_checks nil i l u Success
    | Do_Checks_True_Index: forall ck i l u cks,
        do_flagged_index_check ck i l u Success ->
        do_flagged_index_checks cks i l u Success ->
        do_flagged_index_checks (ck :: cks) i l u Success
    | Do_Checks_False_Head_Index: forall ck i l u msg cks,
        do_flagged_index_check ck i l u (Exception msg) ->
        do_flagged_index_checks (ck :: cks) i l u (Exception msg)
    | Do_Checks_False_Tail_Index: forall ck i l u cks msg,
        do_flagged_index_check ck i l u Success ->
        do_flagged_index_checks cks i l u (Exception msg) ->
        do_flagged_index_checks (ck :: cks) i l u (Exception msg).


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

Inductive eval_expr_x: stack -> expression_x -> Return value -> Prop :=
    | Eval_E_Literal_X: forall l v s ast_num,
        eval_literal l = v ->
        eval_expr_x s (E_Literal_X ast_num l nil) (Normal v)
    | Eval_E_Name_X: forall s n v ast_num,
        eval_name_x s n v ->
        eval_expr_x s (E_Name_X ast_num n nil) v
    | Eval_E_Binary_Operation_RTE_E1_X: forall s e1 msg ast_num op e2 checkflags,
        eval_expr_x s e1 (Run_Time_Error msg) ->
        eval_expr_x s (E_Binary_Operation_X ast_num op e1 e2 checkflags) (Run_Time_Error msg)
    | Eval_E_Binary_Operation_RTE_E2_X: forall s e1 v1 e2 msg ast_num op checkflags,
        eval_expr_x s e1 (Normal v1) ->
        eval_expr_x s e2 (Run_Time_Error msg) ->
        eval_expr_x s (E_Binary_Operation_X ast_num op e1 e2 checkflags) (Run_Time_Error msg)
    | Eval_E_Binary_Operation_RTE_Bin_X: forall s e1 v1 e2 v2 checkflags op msg ast_num,
        eval_expr_x s e1 (Normal v1) ->
        eval_expr_x s e2 (Normal v2) ->
        do_flagged_checks_on_binop checkflags op v1 v2 (Exception msg) ->
        eval_expr_x s (E_Binary_Operation_X ast_num op e1 e2 checkflags) (Run_Time_Error msg)
    | Eval_E_Binary_Operation_X: forall s e1 v1 e2 v2 checkflags op v ast_num,
        eval_expr_x s e1 (Normal v1) ->
        eval_expr_x s e2 (Normal v2) ->
        do_flagged_checks_on_binop checkflags op v1 v2 Success ->
        Val.binary_operation op v1 v2 = Some v ->
        eval_expr_x s (E_Binary_Operation_X ast_num op e1 e2 checkflags) (Normal v)
    | Eval_E_Unary_Operation_RTE_E_X: forall s e msg ast_num op checkflags,
        eval_expr_x s e (Run_Time_Error msg) ->
        eval_expr_x s (E_Unary_Operation_X ast_num op e checkflags) (Run_Time_Error msg)
    | Eval_E_Unary_Operation_RTE_X: forall s e v checkflags op msg ast_num,
        eval_expr_x s e (Normal v) ->
        do_flagged_checks_on_unop checkflags op v (Exception msg) ->
        eval_expr_x s (E_Unary_Operation_X ast_num op e checkflags) (Run_Time_Error msg)
    | Eval_E_Unary_Operation_X: forall s e v checkflags op v1 ast_num,
        eval_expr_x s e (Normal v) ->
        do_flagged_checks_on_unop checkflags op v Success ->
        Val.unary_operation op v = Some v1 ->
        eval_expr_x s (E_Unary_Operation_X ast_num op e checkflags) (Normal v1)

with eval_name_x: stack -> name_x -> Return value -> Prop :=
    | Eval_E_Identifier_X: forall x s v ast_num, 
        fetchG x s = Some v ->
        eval_name_x s (E_Identifier_X ast_num x nil) (Normal v)
    | Eval_E_Indexed_Component_RTE_E_X: forall s e msg ast_num x_ast_num x checkflags,
        eval_expr_x s e (Run_Time_Error msg) ->
        eval_name_x s (E_Indexed_Component_X ast_num x_ast_num x e checkflags) (Run_Time_Error msg)
    | Eval_E_Indexed_Component_RTE_Index_X: forall s e i x l u a checkflags ast_num x_ast_num, 
        eval_expr_x s e (Normal (BasicV (Int i))) ->
        fetchG x s = Some (AggregateV (ArrayV (l, u, a))) ->
        do_flagged_index_checks checkflags i l u (Exception RTE_Index) ->
        eval_name_x s (E_Indexed_Component_X ast_num x_ast_num x e checkflags) Index_Error
    | Eval_E_Indexed_Component_X: forall s e i x l u a checkflags v ast_num x_ast_num, 
        eval_expr_x s e (Normal (BasicV (Int i))) ->
        fetchG x s = Some (AggregateV (ArrayV (l, u, a))) ->
        do_flagged_index_checks checkflags i l u Success ->
        array_select a i = Some v ->
        eval_name_x s (E_Indexed_Component_X ast_num x_ast_num x e checkflags) (Normal (BasicV v))
    | Eval_E_Selected_Component_X: forall x s r f v ast_num x_ast_num,
        fetchG x s = Some (AggregateV (RecordV r)) ->
        record_select r f = Some v ->
        eval_name_x s (E_Selected_Component_X ast_num x_ast_num x f nil) (Normal (BasicV v)).

(** ** Statement Evaluation Semantics *)

(** *** Copy Out *)
(** Stack manipulation for procedure calls and return *)

Inductive copy_out_x: stack -> frame -> list parameter_specification_x -> list expression_x -> stack -> Prop :=
    | Copy_Out_Nil_X : forall s f, 
        copy_out_x s f nil nil s
    | Copy_Out_Cons_Out_X: forall s s' s'' v f param lparam lexp x ast_num1 ast_num2,
        param.(parameter_mode_x) = Out ->
        fetch param.(parameter_name_x) f = Some v ->
        updateG s x v = Some s' ->
        copy_out_x s' f lparam lexp s'' ->
        copy_out_x s f (param :: lparam) ((E_Name_X ast_num1 (E_Identifier_X ast_num2 x nil) nil) :: lexp) s''
    | Copy_Out_Cons_In_X: forall s s' f param lparam lexp e,
        param.(parameter_mode_x) = In ->
        copy_out_x s f lparam lexp s' ->
        copy_out_x s f (param :: lparam) (e :: lexp) s'.

(** *** Copy In *)
Inductive copy_in_x: stack -> frame -> list parameter_specification_x -> list expression_x -> Return frame -> Prop :=
    | Copy_In_Nil_X : forall s f, 
        copy_in_x s f nil nil (Normal f)
    | Copy_In_Cons_Out_X: forall param s f lparam le f' ast_num x_ast_num x,
        param.(parameter_mode_x) = Out ->
        copy_in_x s f lparam le (Normal f') ->
        copy_in_x s f (param::lparam) ((E_Name_X ast_num (E_Identifier_X x_ast_num x nil) nil) :: le) (Normal (push f' param.(parameter_name_x) Undefined))
    | Copy_In_Cons_Out_E_X: forall param s f lparam le msg ast_num x_ast_num x,
        param.(parameter_mode_x) = Out ->
        copy_in_x s f lparam le (Run_Time_Error msg) ->
        copy_in_x s f (param::lparam) ((E_Name_X ast_num (E_Identifier_X x_ast_num x nil) nil)::le) (Run_Time_Error msg)
    | Copy_In_Cons_In_X: forall param s e v f lparam le f',
        param.(parameter_mode_x) = In ->
        eval_expr_x s e (Normal v) ->
        copy_in_x s f lparam le (Normal f') ->
        copy_in_x s f (param::lparam) (e::le) (Normal (push f' param.(parameter_name_x) v))
    | Copy_In_Cons_In_E1_X: forall param s e msg f lparam le,
        param.(parameter_mode_x) = In ->
        eval_expr_x s e (Run_Time_Error msg) ->
        copy_in_x s f (param::lparam) (e::le) (Run_Time_Error msg)
    | Copy_In_Cons_In_E2_X: forall param s e v f lparam le msg,
        param.(parameter_mode_x) = In ->
        eval_expr_x s e (Normal v) ->
        copy_in_x s f lparam le (Run_Time_Error msg) ->
        copy_in_x s f (param::lparam) (e::le) (Run_Time_Error msg).

(** Inductive semantic of declarations. [eval_decl s nil decl
    rsto] means that rsto is the frame to be pushed on s after
    evaluating decl, sto is used as an accumulator for building
    the frame.
 *)

(** ** Declaration Evaluation Semantics *)
Inductive eval_decl_x: stack -> frame -> declaration_x -> Return frame -> Prop :=
    | Eval_Decl_Null_X: forall s f,
        eval_decl_x s f D_Null_Declaration_X (Normal f)
    | Eval_Decl_Type_X: forall s f ast_num t,
        eval_decl_x s f (D_Type_Declaration_X ast_num t) (Normal f)
    | Eval_Decl_E_X: forall d e f s msg ast_num,
        d.(initialization_expression_x) = Some e ->
        eval_expr_x (f :: s) e (Run_Time_Error msg) ->
        eval_decl_x s f (D_Object_Declaration_X ast_num d) (Run_Time_Error msg)
    | Eval_Decl_X: forall d e f s v ast_num,
        d.(initialization_expression_x) = Some e ->
        eval_expr_x (f :: s) e (Normal v) ->
        eval_decl_x s f (D_Object_Declaration_X ast_num d) (Normal (push f d.(object_name_x) v))
    | Eval_UndefDecl_X: forall d s f ast_num,
        d.(initialization_expression_x) = None ->
        eval_decl_x s f (D_Object_Declaration_X ast_num d) (Normal (push f d.(object_name_x) Undefined))
    | Eval_Decl_Proc_X: forall s f ast_num p,
        eval_decl_x s f (D_Procedure_Declaration_X ast_num p) (Normal f)
    | Eval_Decl_Seq_E_X: forall s f d1 msg ast_num d2,
        eval_decl_x s f d1 (Run_Time_Error msg) ->
        eval_decl_x s f (D_Seq_Declaration_X ast_num d1 d2) (Run_Time_Error msg)
    | Eval_Decl_Seq_X: forall s f d1 f' d2 f'' ast_num,
        eval_decl_x s f d1 (Normal f') ->
        eval_decl_x s f d2 f'' ->
        eval_decl_x s f (D_Seq_Declaration_X ast_num d1 d2) f''.
(*  | Eval_Decl_Proc_X: forall s sto ast_num p,
        eval_decl_x s sto (D_Procedure_Declaration_X ast_num p) (Normal ((procedure_name_x p,Procedure p)::sto))
    | Eval_Decl_Type_X: forall s sto ast_num t,
        eval_decl_x s sto (D_Type_Declaration_X ast_num t) (Normal ((type_name_x t, TypeDef t) :: sto))
*)

(** Inductive semantic of statement and declaration

   in a statement evaluation, whenever a run time error is detected in
   the evaluation of its sub-statements or sub-component, the
   evaluation is terminated and return a run time error; otherwise,
   evaluate the statement into a normal state.

 *)

Inductive eval_stmt_x: symboltable -> stack -> statement_x -> Return stack -> Prop := 
    | Eval_S_Null_X: forall st s,
        eval_stmt_x st s S_Null_X (Normal s)
    | Eval_S_Assignment_RTE_X: forall s e msg st ast_num x,
        eval_expr_x s e (Run_Time_Error msg) ->
        eval_stmt_x st s (S_Assignment_X ast_num x e) (Run_Time_Error msg)
    | Eval_S_Assignment_X: forall s e v x s1 st ast_num,
        eval_expr_x s e (Normal v) ->
        storeUpdate_x s x v s1 ->
        eval_stmt_x st s (S_Assignment_X ast_num x e) s1
    | Eval_S_If_RTE_X: forall s b msg st ast_num c1 c2,
        eval_expr_x s b (Run_Time_Error msg) ->
        eval_stmt_x st s (S_If_X ast_num b c1 c2) (Run_Time_Error msg)
    | Eval_S_If_True_X: forall s b st c1 s1 ast_num c2,
        eval_expr_x s b (Normal (BasicV (Bool true))) ->
        eval_stmt_x st s c1 s1 ->
        eval_stmt_x st s (S_If_X ast_num b c1 c2) s1
    | Eval_S_If_False_X: forall s b st c2 s1 ast_num c1,
        eval_expr_x s b (Normal (BasicV (Bool false))) ->
        eval_stmt_x st s c2 s1 ->
        eval_stmt_x st s (S_If_X ast_num b c1 c2) s1
    | Eval_S_While_Loop_RTE_X: forall s b msg st ast_num c,
        eval_expr_x s b (Run_Time_Error msg) ->
        eval_stmt_x st s (S_While_Loop_X ast_num b c) (Run_Time_Error msg)
    | Eval_S_While_Loop_True_RTE_X: forall s b st c msg ast_num,
        eval_expr_x s b (Normal (BasicV (Bool true))) ->
        eval_stmt_x st s c (Run_Time_Error msg) ->
        eval_stmt_x st s (S_While_Loop_X ast_num b c) (Run_Time_Error msg)
    | Eval_S_While_Loop_True_X: forall s b st c s1 ast_num s2,
        eval_expr_x s b (Normal (BasicV (Bool true))) ->
        eval_stmt_x st s c (Normal s1) ->
        eval_stmt_x st s1 (S_While_Loop_X ast_num b c) s2 ->
        eval_stmt_x st s (S_While_Loop_X ast_num b c) s2
    | Eval_S_While_Loop_False_X: forall s b st ast_num c,
        eval_expr_x s b (Normal (BasicV (Bool false))) ->
        eval_stmt_x st s (S_While_Loop_X ast_num b c) (Normal s)
    | Eval_S_Proc_RTE_Args_X: forall p st n pb s args msg ast_num p_ast_num,
        fetch_proc p st = Some (n, pb) ->
        copy_in_x s (newFrame n) (procedure_parameter_profile_x pb) args (Run_Time_Error msg) ->
        eval_stmt_x st s (S_Procedure_Call_X ast_num p_ast_num p args) (Run_Time_Error msg)
    | Eval_S_Proc_RTE_Decl_X: forall p st n pb s args f intact_s s1 msg ast_num p_ast_num,
        fetch_proc p st = Some (n, pb) ->
        copy_in_x s (newFrame n) (procedure_parameter_profile_x pb) args (Normal f) ->
        cut_until s n intact_s s1 -> (* s = intact_s ++ s1 *)
        eval_decl_x s1 f (procedure_declarative_part_x pb) (Run_Time_Error msg) ->
        eval_stmt_x st s (S_Procedure_Call_X ast_num p_ast_num p args) (Run_Time_Error msg)
    | Eval_S_Proc_RTE_Body_X: forall p st n pb s args f intact_s s1 f1 msg ast_num p_ast_num,
        fetch_proc p st = Some (n, pb) ->
        copy_in_x s (newFrame n) (procedure_parameter_profile_x pb) args (Normal f) ->
        cut_until s n intact_s s1 -> (* s = intact_s ++ s1 *)
        eval_decl_x s1 f (procedure_declarative_part_x pb) (Normal f1) ->
        eval_stmt_x st (f1 :: s1) (procedure_statements_x pb) (Run_Time_Error msg) ->
        eval_stmt_x st s (S_Procedure_Call_X ast_num p_ast_num p args) (Run_Time_Error msg)
    | Eval_S_Proc_X: forall p st n pb s args f intact_s s1 f1 s2 locals_section params_section s3 s4 ast_num p_ast_num,
        fetch_proc p st = Some (n, pb) ->
        copy_in_x s (newFrame n) (procedure_parameter_profile_x pb) args (Normal f) ->
        cut_until s n intact_s s1 -> (* s = intact_s ++ s1 *)
        eval_decl_x s1 f (procedure_declarative_part_x pb) (Normal f1) ->          
        eval_stmt_x st (f1 :: s1) (procedure_statements_x pb) (Normal s2) ->
        s2 = (n, locals_section ++ params_section) :: s3 -> (* extract parameters from local frame *)
        length (store_of f) = length params_section ->
        copy_out_x (intact_s ++ s3) (n, params_section) (procedure_parameter_profile_x pb) args s4 ->
        eval_stmt_x st s (S_Procedure_Call_X ast_num p_ast_num p args) (Normal s4)
    | Eval_S_Sequence_RTE_X: forall st s c1 msg ast_num c2,
        eval_stmt_x st s c1 (Run_Time_Error msg) ->
        eval_stmt_x st s (S_Sequence_X ast_num c1 c2) (Run_Time_Error msg)
    | Eval_S_Sequence_X: forall st s c1 s1 c2 s2 ast_num,
        eval_stmt_x st s c1 (Normal s1) ->
        eval_stmt_x st s1 c2 s2 ->
        eval_stmt_x st s (S_Sequence_X ast_num c1 c2) s2

with storeUpdate_x: stack -> name_x -> value -> Return stack -> Prop := 
    | SU_Identifier_X: forall s x v s1 ast_num,
        updateG s x v = Some s1 ->
        storeUpdate_x s (E_Identifier_X ast_num x nil) v (Normal s1)
    | SU_Indexed_Component_RTE_E_X: forall x s a e msg ast_num x_ast_num checkflags v,
        fetchG x s = Some (AggregateV (ArrayV a)) ->
        eval_expr_x s e (Run_Time_Error msg) ->
        storeUpdate_x s (E_Indexed_Component_X ast_num x_ast_num x e checkflags) v (Run_Time_Error msg)
    | SU_Indexed_Component_RTE_Index_X: forall x s l u a e i checkflags ast_num x_ast_num v,
        fetchG x s = Some (AggregateV (ArrayV (l, u, a))) ->
        eval_expr_x s e (Normal (BasicV (Int i))) ->
        do_flagged_index_checks checkflags i l u (Exception RTE_Index) ->
        storeUpdate_x s (E_Indexed_Component_X ast_num x_ast_num x e checkflags) v (Run_Time_Error RTE_Index)
    | SU_Indexed_Component_X: forall x s l u a e i checkflags v a1 s1 ast_num x_ast_num,
        fetchG x s = Some (AggregateV (ArrayV (l, u, a))) ->
        eval_expr_x s e (Normal (BasicV (Int i))) ->
        do_flagged_index_checks checkflags i l u Success ->
        arrayUpdate a i v = a1 -> (* a[i] := v *)
        updateG s x (AggregateV (ArrayV (l, u, a1))) = Some s1 ->
        storeUpdate_x s (E_Indexed_Component_X ast_num x_ast_num x e checkflags) (BasicV v) (Normal s1)
    | SU_Selected_Component_X: forall r s r1 f v r2 s1 ast_num r_ast_num,
        fetchG r s = Some (AggregateV (RecordV r1)) ->
        recordUpdate r1 f v = r2 -> (* r1.f := v *)
        updateG s r (AggregateV (RecordV r2)) = Some s1 ->
        storeUpdate_x s (E_Selected_Component_X ast_num r_ast_num r f nil) (BasicV v) (Normal s1).













