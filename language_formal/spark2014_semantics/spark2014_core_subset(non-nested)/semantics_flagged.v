Require Export checks.
Require Export language_flagged.
Require Export semantics.

Module Entry_Value_Stored_X <: ENTRY.

  Definition T := value_stored procedure_declaration_x type_declaration_x.

End Entry_Value_Stored_X.

Module STACK_X := STORE(Entry_Value_Stored_X).

Import STACK_X.


(** interpret the literal expressions *)
Definition eval_literal_x (l: literal_x): value :=
    match l with
    | Integer_Literal_X v => BasicV (Int v)
    | Boolean_Literal_X v => BasicV (Bool v)
    end.

(** * Relational Semantics (big-step) *)

(** ** Expression semantics *)
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
        eval_literal_x l = v ->
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
        fetchG x s = Some (Value v) ->
        eval_name_x s (E_Identifier_X ast_num x nil) (Normal v)
    | Eval_E_Indexed_Component_RTE_E_X: forall s e msg ast_num x_ast_num x checkflags,
        eval_expr_x s e (Run_Time_Error msg) ->
        eval_name_x s (E_Indexed_Component_X ast_num x_ast_num x e checkflags) (Run_Time_Error msg)
    | Eval_E_Indexed_Component_RTE_Index_X: forall s e i x l u a checkflags ast_num x_ast_num, 
        eval_expr_x s e (Normal (BasicV (Int i))) ->
        fetchG x s = Some (Value (AggregateV (ArrayV (l, u, a)))) ->
        do_flagged_index_checks checkflags i l u (Exception RTE_Index) ->
        eval_name_x s (E_Indexed_Component_X ast_num x_ast_num x e checkflags) Index_Error
    | Eval_E_Indexed_Component_X: forall s e i x l u a checkflags v ast_num x_ast_num, 
        eval_expr_x s e (Normal (BasicV (Int i))) ->
        fetchG x s = Some (Value (AggregateV (ArrayV (l, u, a)))) ->
        do_flagged_index_checks checkflags i l u Success ->
        array_select a i = Some v ->
        eval_name_x s (E_Indexed_Component_X ast_num x_ast_num x e checkflags) (Normal (BasicV v))
    | Eval_E_Selected_Component_X: forall x s r f v ast_num x_ast_num,
        fetchG x s = Some (Value (AggregateV (RecordV r))) ->
        record_select r f = Some v ->
        eval_name_x s (E_Selected_Component_X ast_num x_ast_num x f nil) (Normal (BasicV v)).

(** * Statement semantics *)

(** ** Stack manipulation for procedure calls and return *)

(** [Copy_out prefix lparams lexp s s'] means that s' is the result of
    copying Out params of the currently finished procedure of prefix
    into there output variables. More precisely:
  - [prefix] is a portion of stack where only the parameters of the
    procedure are stored;
  - [lparams] is the static specification of the parameters of the
    procedure;
  - [lexp] is the list of original expressions given as parameter of
    the procedure (this is where one can find in which variables "out"
    parameters must be copied);
  - [s] is the portion of the stack which needs to be updated and
    returned by the procedure, more precisely: it contains the global
    parameters + the local environment of the colling procedure;
  - [s'] is the resulting state. *)

Inductive copy_out_x: store -> list parameter_specification_x -> list expression_x -> stack -> stack -> Prop :=
    | Copy_Out_Nil_X : forall prf σ, 
        copy_out_x prf nil nil σ σ
    | Copy_Out_Cons_Out_X: forall σ σ' σ'' v prf param lparam lexp x ast_num1 ast_num2,
        param.(parameter_mode_x) = Out ->
        fetch param.(parameter_name_x) prf = Some v ->
        updateG σ x v = Some σ' ->
        copy_out_x prf lparam lexp σ' σ'' ->
        copy_out_x prf (param::lparam) ((E_Name_X ast_num1 (E_Identifier_X ast_num2 x nil) nil) :: lexp) σ σ''
    | Copy_Out_Cons_In_X: forall σ σ' prf param lparam lexp e,
        param.(parameter_mode_x) = In ->
        copy_out_x prf lparam lexp σ σ' ->
        copy_out_x prf (param::lparam) (e :: lexp) σ σ'.

(** [Copy_in s lparams lexp frame] means the frame is the portion of
    stack to push on the stack to start evaluating the procedure
    having [lparams] as parameters spcification. More precisely,
    [frame] contains the value of the formal parameters described by
    [lpamrams]. These values are computed from the list of arguments
    [lexp]. Only "In" parameters are evaluated, "Out" parameters are
    set to [Undefined]. *)

Inductive copy_in_x: stack -> list parameter_specification_x -> list expression_x -> Return store -> Prop :=
    | Copy_In_Nil_X : forall σ, 
        copy_in_x σ nil nil (Normal nil)
    | Copy_In_Cons_Out_X: forall σ param lparam lexp frame ast_num1 ast_num2 x,
        param.(parameter_mode_x) = Out ->
        copy_in_x σ lparam lexp (Normal frame) ->
        copy_in_x σ (param::lparam) ((E_Name_X ast_num1 (E_Identifier_X ast_num2 x nil) nil)::lexp) (Normal ((param.(parameter_name_x),Undefined)::frame))
    | Copy_In_Cons_Out_E_X: forall σ param lparam lexp msg ast_num1 ast_num2 x,
        param.(parameter_mode_x) = Out ->
        copy_in_x σ lparam lexp (Run_Time_Error msg) ->
        copy_in_x σ (param::lparam) ((E_Name_X ast_num1 (E_Identifier_X ast_num2 x nil) nil)::lexp) (Run_Time_Error msg)
    | Copy_In_Cons_In_X: forall σ param e v lparam lexp frame,
        param.(parameter_mode_x) = In ->
        eval_expr_x σ e (Normal v) ->
        copy_in_x σ lparam lexp (Normal frame) ->
        copy_in_x σ (param::lparam) (e::lexp) (Normal ((param.(parameter_name_x),Value v)::frame))
    | Copy_In_Cons_In_E1_X: forall σ param e msg lparam lexp,
        param.(parameter_mode_x) = In ->
        eval_expr_x σ e (Run_Time_Error msg) ->
        copy_in_x σ (param::lparam) (e::lexp) (Run_Time_Error msg)
    | Copy_In_Cons_In_E2_X: forall σ param e v lparam lexp msg,
        param.(parameter_mode_x) = In ->
        eval_expr_x σ e (Normal v) ->
        copy_in_x σ lparam lexp (Run_Time_Error msg) ->
        copy_in_x σ (param::lparam) (e::lexp) (Run_Time_Error msg).

(** *** Inductive semantic of declarations. [eval_decl s nil decl
        rsto] means that rsto is the frame to be pushed on s after
        evaluating decl, sto is used as an accumulator for building
        the frame.
 *)

Inductive eval_decl_x: stack -> store -> declaration_x -> Return store -> Prop :=
    | Eval_Decl_E_X: forall d e sto s msg ast_num,
        d.(initialization_expression_x) = Some e ->
        eval_expr_x (sto::s) e (Run_Time_Error msg) ->
        eval_decl_x s sto (D_Object_Declaration_X ast_num d) (Run_Time_Error msg)
    | Eval_Decl_X: forall d e sto s v ast_num,
        d.(initialization_expression_x) = Some e ->
        eval_expr_x (sto::s) e (Normal v) ->
        eval_decl_x s sto (D_Object_Declaration_X ast_num d) (Normal ((d.(object_name_x), Value v) :: sto))
    | Eval_UndefDecl_X: forall d s sto ast_num,
        d.(initialization_expression_x) = None ->
        eval_decl_x s sto (D_Object_Declaration_X ast_num d) (Normal ((d.(object_name_x), Undefined) :: sto))
    | Eval_Decl_Proc_X: forall s sto ast_num p,
        eval_decl_x s sto (D_Procedure_Declaration_X ast_num p) (Normal ((procedure_name_x p,Procedure p)::sto))
    | Eval_Decl_Type_X: forall s sto ast_num t,
        eval_decl_x s sto (D_Type_Declaration_X ast_num t) (Normal ((type_name_x t, TypeDef t) :: sto)).

Inductive eval_decls_x: stack -> store -> list declaration_x -> Return store -> Prop :=
    | Eval_Decls_Nil_X: forall s sto,
        eval_decls_x s sto nil (Normal sto)
    | Eval_Decls_RTE_X: forall s sto d msg ld,
        eval_decl_x s sto d (Run_Time_Error msg) ->
        eval_decls_x s sto (d :: ld) (Run_Time_Error msg)
    | Eval_Decls_X: forall s sto d sto1 ld sto2,
        eval_decl_x s sto d (Normal sto1) ->
        eval_decls_x s sto1 ld sto2 ->
        eval_decls_x s sto (d :: ld) sto2.

(** ** Inductive semantic of statement and declaration

   in a statement evaluation, whenever a run time error is detected in
   the evaluation of its sub-statements or sub-component, the
   evaluation is terminated and return a run time error; otherwise,
   evaluate the statement into a normal state.

 *)

Inductive eval_stmt_x: stack -> statement_x -> Return stack -> Prop := 
    | Eval_S_Null_X: forall s ast_num,
        eval_stmt_x s (S_Null_X ast_num) (Normal s)
    | Eval_S_Assignment_RTE_X: forall s e msg ast_num x,
        eval_expr_x s e (Run_Time_Error msg) ->
        eval_stmt_x s (S_Assignment_X ast_num x e) (Run_Time_Error msg)
    | Eval_S_Assignment_X: forall s e v x s1 ast_num,
        eval_expr_x s e (Normal v) ->
        storeUpdate_x s x v s1 ->
        eval_stmt_x s (S_Assignment_X ast_num x e) s1
    | Eval_S_If_RTE_X: forall s b msg ast_num c1 c2,
        eval_expr_x s b (Run_Time_Error msg) ->
        eval_stmt_x s (S_If_X ast_num b c1 c2) (Run_Time_Error msg)
    | Eval_S_If_True_X: forall s b c1 s1 ast_num c2,
        eval_expr_x s b (Normal (BasicV (Bool true))) ->
        eval_stmt_x s c1 s1 ->
        eval_stmt_x s (S_If_X ast_num b c1 c2) s1
    | Eval_S_If_False_X: forall s b c2 s1 ast_num c1,
        eval_expr_x s b (Normal (BasicV (Bool false))) ->
        eval_stmt_x s c2 s1 ->
        eval_stmt_x s (S_If_X ast_num b c1 c2) s1
    | Eval_S_While_Loop_RTE_X: forall s b msg ast_num c,
        eval_expr_x s b (Run_Time_Error msg) ->
        eval_stmt_x s (S_While_Loop_X ast_num b c) (Run_Time_Error msg)
    | Eval_S_While_Loop_True_RTE_X: forall s b c msg ast_num,
        eval_expr_x s b (Normal (BasicV (Bool true))) ->
        eval_stmt_x s c (Run_Time_Error msg) ->
        eval_stmt_x s (S_While_Loop_X ast_num b c) (Run_Time_Error msg)
    | Eval_S_While_Loop_True_X: forall s b c s1 ast_num s2,
        eval_expr_x s b (Normal (BasicV (Bool true))) ->
        eval_stmt_x s c (Normal s1) ->
        eval_stmt_x s1 (S_While_Loop_X ast_num b c) s2 ->
        eval_stmt_x s (S_While_Loop_X ast_num b c) s2
    | Eval_S_While_Loop_False_X: forall s b ast_num c,
        eval_expr_x s b (Normal (BasicV (Bool false))) ->
        eval_stmt_x s (S_While_Loop_X ast_num b c) (Normal s)
    | Eval_S_Proc_RTE_Args_X: forall pid s pb args msg ast_num1 ast_num2,
        fetchG pid s = Some (Procedure pb) ->
        copy_in_x s (procedure_parameter_profile_x pb) args (Run_Time_Error msg) ->
        eval_stmt_x s (S_ProcCall_X ast_num1 ast_num2 pid args) (Run_Time_Error msg)
    | Eval_S_Proc_RTE_Decl_X: forall pid s pb args newframe s_intact s1 msg ast_num1 ast_num2,
        fetchG pid s = Some (Procedure pb) ->
        copy_in_x s (procedure_parameter_profile_x pb) args (Normal newframe) ->
        cut_until s pid s_intact s1 -> (* s = s_intact ++ s1 *)
        eval_decls_x s1 newframe (procedure_declarative_part_x pb) (Run_Time_Error msg) ->
        eval_stmt_x s (S_ProcCall_X ast_num1 ast_num2 pid args) (Run_Time_Error msg)
    | Eval_S_Proc_RTE_Body_X: forall pid s pb args newframe s_intact s1 newframe1 msg ast_num1 ast_num2,
        fetchG pid s = Some (Procedure pb) ->
        copy_in_x s (procedure_parameter_profile_x pb) args (Normal newframe) ->
        cut_until s pid s_intact s1 -> (* s = s_intact ++ s1 *)
        eval_decls_x s1 newframe (procedure_declarative_part_x pb) (Normal newframe1) ->
        eval_stmt_x (newframe1 :: s1) (procedure_statements_x pb) (Run_Time_Error msg) ->
        eval_stmt_x s (S_ProcCall_X ast_num1 ast_num2 pid args) (Run_Time_Error msg)
    | Eval_S_Proc_X: forall pid s pb args newframe s_intact s1 newframe1 s2
                          slocal prefix s3 s4 ast_num1 ast_num2,
        fetchG pid s = Some (Procedure pb) ->
        copy_in_x s (procedure_parameter_profile_x pb) args (Normal newframe) ->
        cut_until s pid s_intact s1 -> (* s = s_intact ++ s1 *)
        eval_decls_x s1 newframe (procedure_declarative_part_x pb) (Normal newframe1) ->          
        eval_stmt_x (newframe1 :: s1) (procedure_statements_x pb) (Normal s2) ->
        s2 = (slocal ++ prefix) :: s3 -> (* extract parameters from local frame *)
        List.length newframe = List.length prefix ->
        copy_out_x prefix (procedure_parameter_profile_x pb) args (s_intact ++ s3) s4 ->
        eval_stmt_x s (S_ProcCall_X ast_num1 ast_num2 pid args) (Normal s4)
    | Eval_S_Sequence_RTE_X: forall s c1 msg ast_num c2,
        eval_stmt_x s c1 (Run_Time_Error msg) ->
        eval_stmt_x s (S_Sequence_X ast_num c1 c2) (Run_Time_Error msg)
    | Eval_S_Sequence_X: forall s c1 s1 c2 s2 ast_num,
        eval_stmt_x s c1 (Normal s1) ->
        eval_stmt_x s1 c2 s2 ->
        eval_stmt_x s (S_Sequence_X ast_num c1 c2) s2

with storeUpdate_x: stack -> name_x -> value -> Return stack -> Prop := 
    | SU_Identifier_X: forall s x v s1 ast_num,
        updateG s x (Value v) = Some s1 ->
        storeUpdate_x s (E_Identifier_X ast_num x nil) v (Normal s1)
    | SU_Indexed_Component_RTE_E_X: forall x s a e msg ast_num x_ast_num checkflags v,
        fetchG x s = Some (Value (AggregateV (ArrayV a))) ->
        eval_expr_x s e (Run_Time_Error msg) ->
        storeUpdate_x s (E_Indexed_Component_X ast_num x_ast_num x e checkflags) v (Run_Time_Error msg)
    | SU_Indexed_Component_RTE_Index_X: forall x s l u a e i checkflags ast_num x_ast_num v,
        fetchG x s = Some (Value (AggregateV (ArrayV (l, u, a)))) ->
        eval_expr_x s e (Normal (BasicV (Int i))) ->
        do_flagged_index_checks checkflags i l u (Exception RTE_Index) ->
        storeUpdate_x s (E_Indexed_Component_X ast_num x_ast_num x e checkflags) v (Run_Time_Error RTE_Index)
    | SU_Indexed_Component_X: forall x s l u a e i checkflags v a1 s1 ast_num x_ast_num,
        fetchG x s = Some (Value (AggregateV (ArrayV (l, u, a)))) ->
        eval_expr_x s e (Normal (BasicV (Int i))) ->
        do_flagged_index_checks checkflags i l u Success ->
        arrayUpdate a i v = a1 -> (* a[i] := v *)
        updateG s x (Value (AggregateV (ArrayV (l, u, a1)))) = Some s1 ->
        storeUpdate_x s (E_Indexed_Component_X ast_num x_ast_num x e checkflags) (BasicV v) (Normal s1)
    | SU_Selected_Component_X: forall r s r1 f v r2 s1 ast_num r_ast_num,
        fetchG r s = Some (Value (AggregateV (RecordV r1))) ->
        recordUpdate r1 f v = r2 -> (* r1.f := v *)
        updateG s r (Value (AggregateV (RecordV r2))) = Some s1 ->
        storeUpdate_x s (E_Selected_Component_X ast_num r_ast_num r f nil) (BasicV v) (Normal s1).













