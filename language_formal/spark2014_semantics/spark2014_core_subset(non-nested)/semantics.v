Require Export more_list.
Require Export values.
Require Export environment.
Require Export symboltable.
Require Export CpdtTactics.

Module Entry_Value_Stored <: ENTRY.
  Definition T := value.
End Entry_Value_Stored.

Module STACK := STORE(Entry_Value_Stored).
Import STACK.

(** * Run-Time Check Status *)
(** instead of returning only true or false for the run-time checks 
    result, a concrete run-time error is returned if the run-time check
    fails, otherwise return Success;
*)
Inductive check_status :=
    | Success
    | Exception (m: error_type).

(** * Run Time Check Semantics *)
Inductive do_overflow_check_on_binop: binary_operator -> value -> value -> check_status -> Prop :=
    | Do_Overflow_Check_On_Binops: forall op v1 v2 v,
        (* min_signed <= (v1 op v2) <= max_signed *)
        op = Plus \/ op = Minus \/ op = Multiply \/ op = Divide ->
        Val.binary_operation op v1 v2 = Some (BasicV (Int v)) ->
        (Zge_bool v min_signed) && (Zle_bool v max_signed) = true ->
        do_overflow_check_on_binop op v1 v2 Success
    | Do_Overflow_Check_On_Binops_E: forall op v1 v2 v,
        op = Plus \/ op = Minus \/ op = Multiply \/ op = Divide ->
        Val.binary_operation op v1 v2 = Some (BasicV (Int v)) ->
        (Zge_bool v min_signed) && (Zle_bool v max_signed) = false ->
        do_overflow_check_on_binop op v1 v2 (Exception RTE_Overflow).

Inductive do_overflow_check_on_unop: unary_operator -> value -> check_status -> Prop :=
    | Do_Overflow_Check_On_Unops: forall v,
        (Zge_bool (Z.opp v) min_signed) && (Zle_bool (Z.opp v) max_signed) = true ->
        do_overflow_check_on_unop Unary_Minus (BasicV (Int v)) Success
    | Do_Overflow_Check_On_Unops_E: forall v,
        (Zge_bool (Z.opp v) min_signed) && (Zle_bool (Z.opp v) max_signed) = false ->
        do_overflow_check_on_unop Unary_Minus (BasicV (Int v)) (Exception RTE_Overflow).

Inductive do_division_check: binary_operator -> value -> value -> check_status -> Prop :=
    | Do_Division_By_Zero_Check: forall v1 v2,
        (* v2 is not zero *)
        (negb (Zeq_bool v2 0)) = true ->
        do_division_check Divide (BasicV (Int v1)) (BasicV (Int v2)) Success
    | Do_Division_By_Zero_Check_E: forall v1 v2,
        (* v2 is not zero *)
        (negb (Zeq_bool v2 0)) = false ->
        do_division_check Divide (BasicV (Int v1)) (BasicV (Int v2)) (Exception RTE_Division_By_Zero).

Inductive do_range_check: Z -> Z -> Z -> check_status -> Prop :=
    | Do_Range_Check_OK: forall i l u,
        (* i >= l /\ u >= i *)
        (Zge_bool i l) && (Zge_bool u i) = true ->
        do_range_check i l u Success
    | Do_Range_Check_E: forall i l u,
        (Zge_bool i l) && (Zge_bool u i) = false ->
        do_range_check i l u (Exception RTE_Range).

(* verify run time checks on binary / unary operations *)
Inductive do_run_time_check_on_binop: binary_operator -> value -> value -> check_status -> Prop :=
    | Do_Check_On_Binops_O: forall op v1 v2,
        op = Plus \/ op = Minus \/ op = Multiply ->
        do_overflow_check_on_binop op v1 v2 Success ->
        do_run_time_check_on_binop op v1 v2 Success
    | Do_Check_On_Binops_O_E: forall op v1 v2,
        op = Plus \/ op = Minus \/ op = Multiply ->
        do_overflow_check_on_binop op v1 v2 (Exception RTE_Overflow) ->
        do_run_time_check_on_binop op v1 v2 (Exception RTE_Overflow)
    | Do_Check_On_Divide: forall v1 v2,
        do_division_check Divide v1 v2 Success ->
        do_overflow_check_on_binop Divide v1 v2 Success ->
        do_run_time_check_on_binop Divide v1 v2 Success
    | Do_Check_On_Divide_Division_By_Zero_E: forall v1 v2,
        do_division_check Divide v1 v2 (Exception RTE_Division_By_Zero) ->
        do_run_time_check_on_binop Divide v1 v2 (Exception RTE_Division_By_Zero)
    | Do_Check_On_Divide_Overflow_E: forall v1 v2,
        do_division_check Divide v1 v2 Success ->
        do_overflow_check_on_binop Divide v1 v2 (Exception RTE_Overflow) ->
        do_run_time_check_on_binop Divide v1 v2 (Exception RTE_Overflow)
    | Do_Nothing_On_BinOp: forall op v1 v2,
        op <> Plus ->
        op <> Minus ->
        op <> Multiply ->
        op <> Divide ->
        do_run_time_check_on_binop op v1 v2 Success.

Inductive do_run_time_check_on_unop: unary_operator -> value -> check_status -> Prop :=
    | Do_Check_On_Unary_Minus: forall v,
        do_overflow_check_on_unop Unary_Minus v Success ->
        do_run_time_check_on_unop Unary_Minus v Success
    | Do_Check_On_Unary_Minus_E: forall v,
        do_overflow_check_on_unop Unary_Minus v (Exception RTE_Overflow) ->
        do_run_time_check_on_unop Unary_Minus v (Exception RTE_Overflow)
    | Do_Nothing_On_UnOp: forall op v,
        op <> Unary_Minus ->
        do_run_time_check_on_unop op (BasicV (Int v)) Success.

(** given a record value r, get the value of its field f *)
Function record_select (r: list (idnum * basic_value)) (f: idnum): option basic_value :=
    match r with 
    | (f1, v1) :: r1 =>
        if beq_nat f1 f then 
          Some v1
        else
          record_select r1 f
    | nil => None 
    end.

(** given an array value a, get its component value indexed by i *)
Function array_select (a: list (index * basic_value)) (i: Z): option basic_value :=
    match a with 
    | (i0, v0) :: a1 =>
        if Zeq_bool i0 i then
          Some v0
        else
          array_select a1 i
    | nil => None
    end.

(** interpret the literal expressions *)
Definition eval_literal (l: literal): value :=
    match l with
    | Integer_Literal v => BasicV (Int v)
    | Boolean_Literal v => BasicV (Bool v)
    end.

(** * Relational Semantics *)

(** ** Expression Evaluation Semantics *)
(**
    for binary expression and unary expression, if a run time error 
    is detected in any of its child expressions, then return a run
    time error; for binary expression (e1 op e2), if both e1 and e2 
    are evaluated to some normal values, then run-time checks are
    performed according to the checking rules specified for the 
    operator 'op'; Whenever the check fails, a run-time error is 
    detected and the program is terminated, otherwise, normal binary 
    operation result is returned;
*)

Inductive eval_expr: symboltable -> stack -> expression -> Return value -> Prop :=
    | Eval_E_Literal: forall l v st s ast_num,
        eval_literal l = v ->
        eval_expr st s (E_Literal ast_num l) (Normal v)
    | Eval_E_Name: forall s n v st ast_num,
        eval_name st s n v ->
        eval_expr st s (E_Name ast_num n) v
    | Eval_E_Binary_Operation_RTE_E1: forall st s e1 msg ast_num op e2,
        eval_expr st s e1 (Run_Time_Error msg) ->
        eval_expr st s (E_Binary_Operation ast_num op e1 e2) (Run_Time_Error msg)
    | Eval_E_Binary_Operation_RTE_E2: forall st s e1 v1 e2 msg ast_num op,
        eval_expr st s e1 (Normal v1) ->
        eval_expr st s e2 (Run_Time_Error msg) ->
        eval_expr st s (E_Binary_Operation ast_num op e1 e2) (Run_Time_Error msg)
    | Eval_E_Binary_Operation_RTE_Bin: forall st s e1 v1 e2 v2 msg ast_num op,
        eval_expr st s e1 (Normal v1) ->
        eval_expr st s e2 (Normal v2) ->
        do_run_time_check_on_binop op v1 v2 (Exception msg) ->
        eval_expr st s (E_Binary_Operation ast_num op e1 e2) (Run_Time_Error msg)
    | Eval_E_Binary_Operation: forall st s e1 v1 e2 v2 ast_num op v,
        eval_expr st s e1 (Normal v1) ->
        eval_expr st s e2 (Normal v2) ->
        do_run_time_check_on_binop op v1 v2 Success ->
        Val.binary_operation op v1 v2 = Some v ->
        eval_expr st s (E_Binary_Operation ast_num op e1 e2) (Normal v)
    | Eval_E_Unary_Operation_RTE_E: forall st s e msg ast_num op,
        eval_expr st s e (Run_Time_Error msg) ->
        eval_expr st s (E_Unary_Operation ast_num op e) (Run_Time_Error msg)
    | Eval_E_Unary_Operation_RTE: forall st s e v msg ast_num op,
        eval_expr st s e (Normal v) ->
        do_run_time_check_on_unop op v (Exception msg) ->
        eval_expr st s (E_Unary_Operation ast_num op e) (Run_Time_Error msg)
    | Eval_E_Unary_Operation: forall st s e v ast_num op v1,
        eval_expr st s e (Normal v) ->
        do_run_time_check_on_unop op v Success ->
        Val.unary_operation op v = Some v1 ->
        eval_expr st s (E_Unary_Operation ast_num op e) (Normal v1)

with eval_name: symboltable -> stack -> name -> Return value -> Prop :=
    | Eval_E_Identifier: forall x s v st ast_num, 
        fetchG x s = Some v ->
        eval_name st s (E_Identifier ast_num x) (Normal v)
    | Eval_E_Indexed_Component_RTE: forall st s e msg ast_num x_ast_num x,
        eval_expr st s e (Run_Time_Error msg) ->
        eval_name st s (E_Indexed_Component ast_num x_ast_num x e) (Run_Time_Error msg)
    | Eval_E_Indexed_Component_Range_RTE: forall st s e i x_ast_num t l u ast_num x, 
        eval_expr st s e (Normal (BasicV (Int i))) ->
        fetch_exp_type x_ast_num st = Some (Array_Type t) ->
        extract_array_index_range st t (Range l u) ->
        do_range_check i l u (Exception RTE_Range) ->
        eval_name st s (E_Indexed_Component ast_num x_ast_num x e) (Run_Time_Error RTE_Range)
    | Eval_E_Indexed_Component: forall st s e i x_ast_num t l u x a v ast_num, 
        eval_expr st s e (Normal (BasicV (Int i))) ->
        fetch_exp_type x_ast_num st = Some (Array_Type t) -> (*get the array type of x from the symbol table with its ast number x_ast_num *)
        extract_array_index_range st t (Range l u) -> (*given array type t, get its array type declaration from symbol table and extract its range*)
        do_range_check i l u Success -> (*do range check on the index expression i against the range of the array index type*)
        fetchG x s = Some (AggregateV (ArrayV a)) -> (*if the index i is within the range of array index type, first get the array value a*)
        array_select a i = Some v -> (*then get the component value indexed by i from array value a*)
        eval_name st s (E_Indexed_Component ast_num x_ast_num x e) (Normal (BasicV v))
    | Eval_E_Selected_Component: forall x s r f v st ast_num x_ast_num,
        fetchG x s = Some (AggregateV (RecordV r)) ->
        record_select r f = Some v ->
        eval_name st s (E_Selected_Component ast_num x_ast_num x f) (Normal (BasicV v)).
(*
    | Eval_E_Indexed_Component_Range_RTE: forall st s e i x_ast_num t a_ast_num l u typ ast_num x, 
        eval_expr st s e (Normal (BasicV (Int i))) ->
        fetch_exp_type x_ast_num st = Some (Array_Type t) ->
        fetch_type t st = Some (Array_Type_Declaration_Range a_ast_num t (Range l u) typ) ->
        do_range_check i l u (Exception RTE_Range) ->
        eval_name st s (E_Indexed_Component ast_num x_ast_num x e) (Run_Time_Error RTE_Range)
    | Eval_E_Indexed_Component_Range: forall st s e i x_ast_num t a_ast_num l u typ x a v ast_num, 
        eval_expr st s e (Normal (BasicV (Int i))) ->
        fetch_exp_type x_ast_num st = Some (Array_Type t) ->
        fetch_type t st = Some (Array_Type_Declaration_Range a_ast_num t (Range l u) typ) ->        
        do_range_check i l u Success ->
        fetchG x s = Some (AggregateV (ArrayV a)) ->
        array_select a i = Some v ->
        eval_name st s (E_Indexed_Component ast_num x_ast_num x e) (Normal (BasicV v))
*)


(** ** Statement Evaluation Semantics *)

(** Stack Manipulation For Procedure Calls And Return *)

(** [Copy_out st s prefix lparams lexp s'] means that s' is the result of
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

(** *** Copy Out *)
Inductive copy_out: symboltable -> stack -> frame -> list parameter_specification -> list expression -> Return stack -> Prop :=
    | Copy_Out_Nil : forall st s f, 
        copy_out st s f nil nil (Normal s)
    | Copy_Out_Cons_Out: forall param f v ast_num st t s x s' lparam lexp s'' x_ast_num,
        param.(parameter_mode) = Out \/ param.(parameter_mode) = In_Out ->
        fetch param.(parameter_name) f = Some v ->
        fetch_exp_type ast_num st = Some t -> (*get the type of output argument x from the symbol table with its ast number*)
        is_range_constrainted_type t = false -> (*if it's not a range constrainted scalar type, then no range check is needed*)
        updateG s x v = Some s' ->
        copy_out st s' f lparam lexp s'' ->
        copy_out st s f (param :: lparam) ((E_Name ast_num (E_Identifier x_ast_num x)) :: lexp) s''
    | Copy_Out_Cons_Out_Range_RTE: forall param f v ast_num st t l u s lparam x_ast_num x lexp,
        param.(parameter_mode) = Out \/ param.(parameter_mode) = In_Out ->
        fetch param.(parameter_name) f = Some (BasicV (Int v)) ->
        fetch_exp_type ast_num st = Some t -> (*get the type of output argument x from the symbol table with its ast number*)
        extract_subtype_range st t (Range l u) -> (*if it's a range constrainted scalar type, then get its range and do range check before copy out*)
        do_range_check v l u (Exception RTE_Range) ->
        copy_out st s f (param :: lparam) ((E_Name ast_num (E_Identifier x_ast_num x)) :: lexp) (Run_Time_Error RTE_Range)
    | Copy_Out_Cons_Out_Range: forall param f v ast_num st t l u s x s' lparam lexp s'' x_ast_num,
        param.(parameter_mode) = Out \/ param.(parameter_mode) = In_Out ->
        fetch param.(parameter_name) f = Some (BasicV (Int v)) ->
        fetch_exp_type ast_num st = Some t ->
        extract_subtype_range st t (Range l u) ->
        do_range_check v l u Success ->
        updateG s x (BasicV (Int v)) = Some s' ->
        copy_out st s' f lparam lexp s'' ->
        copy_out st s f (param :: lparam) ((E_Name ast_num (E_Identifier x_ast_num x)) :: lexp) s''
    | Copy_Out_Cons_In: forall param st s f lparam lexp s' e,
        param.(parameter_mode) = In ->
        copy_out st s f lparam lexp s' ->
        copy_out st s f (param :: lparam) (e :: lexp) s'.

(** [Copy_in st s f lparams lexp frame] means the frame is the portion
    of stack to push on the stack to start evaluating the procedure
    having [lparams] as parameters spcification. More precisely,
    [frame] contains the value of the formal parameters described by
    [lpamrams]. These values are computed from the list of arguments
    [lexp] starting from the initial frame f. Only "In" and "In Out" 
    parameters are evaluated, "Out" parameters are set to [Undefined]. 
*)

(** start from an empty frame and then push the values of arguments into it *)

(** *** Copy In *)
Inductive copy_in: symboltable -> stack -> frame -> list parameter_specification -> list expression -> Return frame -> Prop :=
    | Copy_In_Nil : forall st s f, 
        copy_in st s f nil nil (Normal f)
    | Copy_In_Cons_Out: forall param st s f f' lparam le f'' ast_num x_ast_num x,
        param.(parameter_mode) = Out ->
        push f param.(parameter_name) Undefined = f' ->
        copy_in st s f' lparam le f'' ->
        copy_in st s f (param :: lparam) ((E_Name ast_num (E_Identifier x_ast_num x)) :: le) f''
    | Copy_In_Cons_In_RTE: forall param st s e msg f lparam le,
        param.(parameter_mode) = In \/ param.(parameter_mode) = In_Out ->
        eval_expr st s e (Run_Time_Error msg) ->
        copy_in st s f (param :: lparam) (e :: le) (Run_Time_Error msg)
    | Copy_In_Cons_In: forall param st s e v f f' lparam le f'',
        param.(parameter_mode) = In \/ param.(parameter_mode) = In_Out ->
        eval_expr st s e (Normal v) ->
        is_range_constrainted_type (param.(parameter_subtype_mark)) = false -> (*there's no need to do range check if the parameter's type is not range constrainted type*)
        push f param.(parameter_name) v = f' ->
        copy_in st s f' lparam le f'' ->
        copy_in st s f (param :: lparam) (e :: le) f''
    | Copy_In_Cons_In_Range_RTE: forall param st s e v l u f lparam le,
        param.(parameter_mode) = In \/ param.(parameter_mode) = In_Out ->
        eval_expr st s e (Normal (BasicV (Int v))) ->
        extract_subtype_range st (param.(parameter_subtype_mark)) (Range l u) ->
        do_range_check v l u (Exception RTE_Range) ->
        copy_in st s f (param :: lparam) (e :: le) (Run_Time_Error RTE_Range)
    | Copy_In_Cons_In_Range: forall param st s e v l u f f' lparam le f'',
        param.(parameter_mode) = In \/ param.(parameter_mode) = In_Out ->
        eval_expr st s e (Normal (BasicV (Int v))) ->
        extract_subtype_range st (param.(parameter_subtype_mark)) (Range l u) -> (*if the parameter's type is a range constrainted type, get its type's range*)
        do_range_check v l u Success -> (*do range check on the value of argument against its corresponding parameter's type range*)
        push f param.(parameter_name) (BasicV (Int v)) = f' ->
        copy_in st s f' lparam le f'' ->
        copy_in st s f (param :: lparam) (e :: le) f''.


(** ** Declaration Evaluation Semantics *)
(** Inductive semantic of declarations [eval_decl st s sto decl rsto] 
    means that rsto is the frame to be pushed on s after evaluating 
    decl, sto is used as an accumulator for building the frame;
 *)

Inductive eval_decl: symboltable -> stack -> frame -> declaration -> Return frame -> Prop :=
    | Eval_Decl_Null: forall st s f,
        eval_decl st s f D_Null_Declaration (Normal f)
    | Eval_Decl_Type: forall st s f ast_num t,
        eval_decl st s f (D_Type_Declaration ast_num t) (Normal f)
    | Eval_Decl_Var_None: forall d st s f ast_num,
        d.(initialization_expression) = None ->
        eval_decl st s f (D_Object_Declaration ast_num d) (Normal (push f d.(object_name) Undefined))
    | Eval_Decl_Var_RTE: forall d e st f s msg ast_num,
        d.(initialization_expression) = Some e ->
        eval_expr st (f :: s) e (Run_Time_Error msg) ->
        eval_decl st s f (D_Object_Declaration ast_num d) (Run_Time_Error msg)
    | Eval_Decl_Var: forall d e st f s v ast_num,
        d.(initialization_expression) = Some e ->
        eval_expr st (f :: s) e (Normal v) ->
        is_range_constrainted_type (d.(object_nominal_subtype)) = false ->
        eval_decl st s f (D_Object_Declaration ast_num d) (Normal (push f d.(object_name) v))
    | Eval_Decl_Var_Range_RTE: forall d e st f s v l u ast_num,
        d.(initialization_expression) = Some e ->
        eval_expr st (f :: s) e (Normal (BasicV (Int v))) ->
        extract_subtype_range st (d.(object_nominal_subtype)) (Range l u) ->
        do_range_check v l u (Exception RTE_Range) ->        
        eval_decl st s f (D_Object_Declaration ast_num d) (Run_Time_Error RTE_Range)
    | Eval_Decl_Var_Range: forall d e st f s v l u ast_num,
        d.(initialization_expression) = Some e ->
        eval_expr st (f :: s) e (Normal (BasicV (Int v))) ->
        extract_subtype_range st (d.(object_nominal_subtype)) (Range l u) ->
        do_range_check v l u Success -> (*for a declared variable, do range check on value of its initialization expression if its declared type is range constrainted type*)
        eval_decl st s f (D_Object_Declaration ast_num d) (Normal (push f d.(object_name) (BasicV (Int v))))
    | Eval_Decl_Proc: forall st s f ast_num p,
        eval_decl st s f (D_Procedure_Body ast_num p) (Normal f)
    | Eval_Decl_Seq_RTE: forall st s f d1 msg ast_num d2,
        eval_decl st s f d1 (Run_Time_Error msg) ->
        eval_decl st s f (D_Seq_Declaration ast_num d1 d2) (Run_Time_Error msg)
    | Eval_Decl_Seq: forall st s f d1 f' d2 f'' ast_num,
        eval_decl st s f d1 (Normal f') ->
        eval_decl st s f d2 f'' ->
        eval_decl st s f (D_Seq_Declaration ast_num d1 d2) f''.


(** update the ith element of array a by value v: a[i] := v *)
Function arrayUpdate (a: list (index * basic_value)) (i: index) (v: basic_value): list (index * basic_value) :=
    match a with
    | (i0, v0)::a1 => 
        if Zeq_bool i0 i then
          (i0, v) :: a1
        else
          (i0, v0) :: (arrayUpdate a1 i v)
    | nil => (i, v) :: nil
    end.

(** update the field f of record r by value v: r.f := v *)
Function recordUpdate (r: list (idnum * basic_value)) (f : idnum) (v: basic_value): list (idnum * basic_value) := 
    match r with 
    | (f1, v1) :: r1 => 
      if beq_nat f1 f then 
        (f1,v) :: r1
      else 
        (f1, v1) :: (recordUpdate r1 f v)
   | nil => (f, v) :: nil
   end.

(** [cut_until s n s' s''] means cutting the stack s until to a frame 
    whose corresponding procedure's nested declaration level is less 
    than n, and s' is a stack with all its frame's corresponding procedure's 
    nested declaration level greater or equal n, and s'' is a stack holds 
    frames whose procedure's nested declaration levels are less than n, 
    and s = s' ++ s'';
*)
Inductive cut_until: stack -> scope_level -> stack -> stack -> Prop :=
    | Cut_Until_Nil: forall n,
        cut_until nil n nil nil
    | Cut_Until_Head: forall f n s,
        (level_of f) < n ->
        cut_until (f :: s) n nil (f :: s) 
    | Cut_Until_Tail: forall f n s s' s'',
        ~ (level_of f < n) ->
        cut_until s n s' s'' -> 
        cut_until (f :: s) n (f :: s') s''.

Lemma cut_until_uniqueness: forall s n intact_s' s' intact_s'' s'',
  cut_until s n intact_s' s' ->
  cut_until s n intact_s'' s'' ->
  intact_s' = intact_s'' /\ s' = s''.
Proof.
  intros s n intact_s' s' intact_s'' s'' H; revert intact_s'' s''.
  induction H; intros;
  match goal with
    | [H: cut_until nil _ _ _ |- _] => inversion H
    | [H: cut_until (?f :: ?s) _ _ _ |- _] => inversion H
  end; smack;
  specialize (IHcut_until _ _ H8); smack.
Qed.

(** in a statement evaluation, whenever a run time error is detected in
    the evaluation of its sub-statements or sub-component, the
    evaluation is terminated and return a run-time error; otherwise,
    evaluate the statement into a normal state.

   - in the evaluation for assignment statement (S_Assignment ast_num x e),

     first, check if it's needed to do range check on the right side (e) 
     of the assignment,
     case 1: (is_range_constrainted_type t = false) means no range check 
     needed for the value of expression e as the type of the left side of
     the assignment is not a range constrainted type, 
     case 2: (extract_subtype_range st t (Range l u)) means left side of
     the assignment is a name expression of range constrainted type whose 
     range is between l and u, so a range check is required on the value 
     of expression e;

     second, if there is no range check required for e, then do expression 
     evaluation directly on e and update the value of x if there is no run-time
     errors during their evaluation;
     if there is a range check required for e, then a range check should be 
     performed on the evaluation value of e before it's assigned to the left side
     (x) of the assignment; 
     
     please note that the range check for the value of expression e is verified 
     against the target type taken from the left side (x) of the assignment, that's
     why the range check for expression e is enforced at the level of assignment 
     statement even though the Do_Range_Check flag is set on the expression e;

   - in the store update storeUpdate_x for indexed component (e.g. a(i):=v) or selected
     component (e.g. r.f := v), 
     
     if the value of array a (or value of record r) is Undefined, then create a new 
     aggregate array value with its ith element having value v (or create a new record 
     value with its field f having value v), and assign this new aggregate value to array 
     variable a (or record variable r);
     
     if the value of array a (or value of record r) is already defined, then update the
     ith element of its array value (or update the filed f of its record value), and assign
     the updated aggregate value to array variable a (or record variable r);

   - in the store update storeUpdate_x for indexed component (e.g. a(i):=v), a
     range check is required to be performed on the value of index expression i
     before it's used to update the array value;
 *)

Inductive eval_stmt: symboltable -> stack -> statement -> Return stack -> Prop := 
    | Eval_S_Null: forall st s,
        eval_stmt st s S_Null (Normal s)
    | Eval_S_Assignment_RTE: forall st s e msg ast_num x,
        eval_expr st s e (Run_Time_Error msg) ->
        eval_stmt st s (S_Assignment ast_num x e) (Run_Time_Error msg)
    | Eval_S_Assignment: forall st s e v x t s1 ast_num,
        eval_expr st s e (Normal v) ->
        fetch_exp_type (name_astnum x) st = Some t ->
        is_range_constrainted_type t = false ->
        storeUpdate st s x v s1 ->
        eval_stmt st s (S_Assignment ast_num x e) s1
    | Eval_S_Assignment_Range_RTE: forall st s e v x t l u ast_num,
        eval_expr st s e (Normal (BasicV (Int v))) ->
        fetch_exp_type (name_astnum x) st = Some t -> (*get the type of the left hand side of the assignment*)
        extract_subtype_range st t (Range l u) -> (*if left hand side is an expression of range constrainted type, then get its range from symbol table*)
        do_range_check v l u (Exception RTE_Range) -> (*do range check on the value of the right hand side expression of the assignment*)
        eval_stmt st s (S_Assignment ast_num x e) (Run_Time_Error RTE_Range)
    | Eval_S_Assignment_Range: forall st s e v x t l u s1 ast_num,
        eval_expr st s e (Normal (BasicV (Int v))) ->
        fetch_exp_type (name_astnum x) st = Some t ->
        extract_subtype_range st t (Range l u) ->
        do_range_check v l u Success ->
        storeUpdate st s x (BasicV (Int v)) s1 ->
        eval_stmt st s (S_Assignment ast_num x e) s1
    | Eval_S_If_RTE: forall st s b msg ast_num c1 c2,
        eval_expr st s b (Run_Time_Error msg) ->
        eval_stmt st s (S_If ast_num b c1 c2) (Run_Time_Error msg)
    | Eval_S_If_True: forall st s b c1 s1 ast_num c2,
        eval_expr st s b (Normal (BasicV (Bool true))) ->
        eval_stmt st s c1 s1 ->
        eval_stmt st s (S_If ast_num b c1 c2) s1
    | Eval_S_If_False: forall st s b c2 s1 ast_num c1,
        eval_expr st s b (Normal (BasicV (Bool false))) ->
        eval_stmt st s c2 s1 ->
        eval_stmt st s (S_If ast_num b c1 c2) s1
    | Eval_S_While_Loop_RTE: forall st s b msg ast_num c,
        eval_expr st s b (Run_Time_Error msg) ->
        eval_stmt st s (S_While_Loop ast_num b c) (Run_Time_Error msg)
    | Eval_S_While_Loop_True_RTE: forall st s b c msg ast_num,
        eval_expr st s b (Normal (BasicV (Bool true))) ->
        eval_stmt st s c (Run_Time_Error msg) ->
        eval_stmt st s (S_While_Loop ast_num b c) (Run_Time_Error msg)
    | Eval_S_While_Loop_True: forall st s b c s1 ast_num s2,
        eval_expr st s b (Normal (BasicV (Bool true))) ->
        eval_stmt st s c (Normal s1) ->
        eval_stmt st s1 (S_While_Loop ast_num b c) s2 ->
        eval_stmt st s (S_While_Loop ast_num b c) s2
    | Eval_S_While_Loop_False: forall st s b ast_num c,
        eval_expr st s b (Normal (BasicV (Bool false))) ->
        eval_stmt st s (S_While_Loop ast_num b c) (Normal s)
    | Eval_S_Proc_RTE_Args: forall p st n pb s args msg ast_num p_ast_num,
        fetch_proc p st = Some (n, pb) ->
        copy_in st s (newFrame n) (procedure_parameter_profile pb) args (Run_Time_Error msg) ->
        eval_stmt st s (S_Procedure_Call ast_num p_ast_num p args) (Run_Time_Error msg)
    | Eval_S_Proc_RTE_Decl: forall p st n pb s args f intact_s s1 msg ast_num p_ast_num,
        fetch_proc p st = Some (n, pb) ->
        copy_in st s (newFrame n) (procedure_parameter_profile pb) args (Normal f) ->
        cut_until s n intact_s s1 -> (* s = intact_s ++ s1 *)
        eval_decl st s1 f (procedure_declarative_part pb) (Run_Time_Error msg) ->
        eval_stmt st s (S_Procedure_Call ast_num p_ast_num p args) (Run_Time_Error msg)
    | Eval_S_Proc_RTE_Body: forall p st n pb s args f intact_s s1 f1 msg ast_num p_ast_num,
        fetch_proc p st = Some (n, pb) ->
        copy_in st s (newFrame n) (procedure_parameter_profile pb) args (Normal f) ->
        cut_until s n intact_s s1 -> (* s = intact_s ++ s1 *)
        eval_decl st s1 f (procedure_declarative_part pb) (Normal f1) ->
        eval_stmt st (f1 :: s1) (procedure_statements pb) (Run_Time_Error msg) ->
        eval_stmt st s (S_Procedure_Call ast_num p_ast_num p args) (Run_Time_Error msg)
    | Eval_S_Proc: forall p st n pb s args f intact_s s1 f1 s2 locals_section params_section s3 s4 ast_num p_ast_num,
        fetch_proc p st = Some (n, pb) ->
        copy_in st s (newFrame n) (procedure_parameter_profile pb) args (Normal f) ->
        cut_until s n intact_s s1 -> (* s = intact_s ++ s1 *)
        eval_decl st s1 f (procedure_declarative_part pb) (Normal f1) ->          
        eval_stmt st (f1 :: s1) (procedure_statements pb) (Normal s2) ->
        s2 = (n, locals_section ++ params_section) :: s3 -> (* extract parameters from local frame *)
        length (store_of f) = length params_section ->
        copy_out st (intact_s ++ s3) (n, params_section) (procedure_parameter_profile pb) args s4 ->
        eval_stmt st s (S_Procedure_Call ast_num p_ast_num p args) s4
    | Eval_S_Sequence_RTE: forall st s c1 msg ast_num c2,
        eval_stmt st s c1 (Run_Time_Error msg) ->
        eval_stmt st s (S_Sequence ast_num c1 c2) (Run_Time_Error msg)
    | Eval_S_Sequence: forall st s c1 s1 c2 s2 ast_num,
        eval_stmt st s c1 (Normal s1) ->
        eval_stmt st s1 c2 s2 ->
        eval_stmt st s (S_Sequence ast_num c1 c2) s2

with storeUpdate: symboltable -> stack -> name -> value -> Return stack -> Prop := 
    | SU_Identifier: forall s x v s1 st ast_num,
        updateG s x v = Some s1 ->
        storeUpdate st s (E_Identifier ast_num x) v (Normal s1)
    | SU_Indexed_Component_RTE_E: forall st s e msg ast_num x_ast_num x v,
        eval_expr st s e (Run_Time_Error msg) ->
        storeUpdate st s (E_Indexed_Component ast_num x_ast_num x e) v (Run_Time_Error msg)
    | SU_Indexed_Component_Range_RTE: forall st s e i x_ast_num t l u ast_num x v,
        eval_expr st s e (Normal (BasicV (Int i))) ->
        fetch_exp_type x_ast_num st = Some (Array_Type t) ->
        extract_array_index_range st t (Range l u) ->
        do_range_check i l u (Exception RTE_Range) ->
        storeUpdate st s (E_Indexed_Component ast_num x_ast_num x e) v (Run_Time_Error RTE_Range)
    | SU_Indexed_Component_Undef: forall st s e i x_ast_num t l u x v s1 ast_num,
        eval_expr st s e (Normal (BasicV (Int i))) ->
        fetch_exp_type x_ast_num st = Some (Array_Type t) ->
        extract_array_index_range st t (Range l u) ->
        do_range_check i l u Success ->
        fetchG x s = Some Undefined ->
        updateG s x (AggregateV (ArrayV ((i, v) :: nil))) = Some s1 ->
        storeUpdate st s (E_Indexed_Component ast_num x_ast_num x e) (BasicV v) (Normal s1)
    | SU_Indexed_Component: forall st s e i x_ast_num t l u x a v a1 s1 ast_num,
        eval_expr st s e (Normal (BasicV (Int i))) ->
        fetch_exp_type x_ast_num st = Some (Array_Type t) ->
        extract_array_index_range st t (Range l u) ->
        do_range_check i l u Success ->
        fetchG x s = Some (AggregateV (ArrayV a)) ->
        arrayUpdate a i v = a1 -> (* a[i] := v *)
        updateG s x (AggregateV (ArrayV a1)) = Some s1 ->
        storeUpdate st s (E_Indexed_Component ast_num x_ast_num x e) (BasicV v) (Normal s1)
    | SU_Selected_Component_Undef: forall r s f v s1 st ast_num r_ast_num,
        fetchG r s = Some Undefined ->
        updateG s r (AggregateV (RecordV ((f, v) :: nil))) = Some s1 -> (* r1.f := v *)
        storeUpdate st s (E_Selected_Component ast_num r_ast_num r f) (BasicV v) (Normal s1)
    | SU_Selected_Component: forall r s r1 f v r2 s1 st ast_num r_ast_num,
        fetchG r s = Some (AggregateV (RecordV r1)) ->
        recordUpdate r1 f v = r2 -> (* r1.f := v *)
        updateG s r (AggregateV (RecordV r2)) = Some s1 ->
        storeUpdate st s (E_Selected_Component ast_num r_ast_num r f) (BasicV v) (Normal s1).
(*
    | SU_Indexed_Component_Range_RTE: forall x s a st e i x_ast_num t a_ast_num l u typ ast_num v, 
        fetchG x s = Some a ->
        eval_expr st s e (Normal (BasicV (Int i))) ->
        fetch_exp_type x_ast_num st = Some (Array_Type t) ->
        fetch_type t st = Some (Array_Type_Declaration_Range a_ast_num t (Range l u) typ) ->
        do_range_check i l u (Exception RTE_Range) ->
        storeUpdate st s (E_Indexed_Component ast_num x_ast_num x e) v (Run_Time_Error RTE_Range)
    | SU_Indexed_Component_Range_Undef: forall x s st e i x_ast_num t a_ast_num l u typ s1 ast_num v, 
        fetchG x s = Some Undefined ->
        eval_expr st s e (Normal (BasicV (Int i))) ->
        fetch_exp_type x_ast_num st = Some (Array_Type t) ->
        fetch_type t st = Some (Array_Type_Declaration_Range a_ast_num t (Range l u) typ) ->
        do_range_check i l u Success ->
        updateG s x (AggregateV (ArrayV ((i, v) :: nil))) = Some s1 ->
        storeUpdate st s (E_Indexed_Component ast_num x_ast_num x e) (BasicV v) (Run_Time_Error RTE_Range)
    | SU_Indexed_Component_Range: forall x s a st e i x_ast_num t a_ast_num l u typ a1 s1 ast_num v, 
        fetchG x s = Some (AggregateV (ArrayV a)) ->
        eval_expr st s e (Normal (BasicV (Int i))) ->
        fetch_exp_type x_ast_num st = Some (Array_Type t) ->
        fetch_type t st = Some (Array_Type_Declaration_Range a_ast_num t (Range l u) typ) ->
        do_range_check i l u Success ->
        arrayUpdate a i v = a1 -> (* a[i] := v *)
        updateG s x (AggregateV (ArrayV a1)) = Some s1 ->
        storeUpdate st s (E_Indexed_Component ast_num x_ast_num x e) (BasicV v) (Normal s1)
*)


(**********************************************************************************************************

(** ** examples *)

Module ExampleProcedures.
(* EXAMPLE 1, v102 is a variable in the scope.
------------------------
procedure P2 () is
  V4 : TYPE5 := 34;
begin
  V102 := 56;
end 
-----------------------
*)
Definition proc1:procedure_declaration := (mkprocedure_declaration
           1 101 nil nil
             (D_Object_declaration
                {|
                  declaration_astnum := 3;
                  object_name := 4;
                  object_nominal_subtype :=  5;
                  initialization_expression := Some (E_Literal 6 (Integer_Literal(34)))
                |}
             )
             (S_Assignment 12 102 (E_Literal 8 (Integer_Literal(56))))).

Definition s1:stack := ((101,Procedure proc1) :: (102, Value (Int(77))) :: nil)::nil.

Definition s2:stack := ((101,Procedure proc1) :: (102, Value (Int(56)))  :: nil)::nil.


Lemma essai: eval_stmt s1 (S_ProcCall 13 101 nil) (Normal s2).
Proof.
  eapply eval_S_Proc; try now (simpl; eauto).
  - simpl.
    instantiate (1 := nil).
    constructor.
  - constructor 1.
    reflexivity.
    
  - econstructor 2.
    + reflexivity.
    + simpl.
      reflexivity.
    + constructor.
      simpl.
      reflexivity.
  - simpl.
    econstructor.
    + econstructor.
      simpl.
      eauto.
    + simpl.
      rewrite app_nil_r.
      reflexivity.
  - simpl.
    constructor 1.
Qed.



(* v102 is a variable in the scope.
procedure P2 () is
  V4 : TYPE5 := 34;
  V5 : TYPE5 := 37;
begin
  V5 := V4 + V5;
  V102 := V5*2;
end 
*)
Definition proc2:procedure_declaration := (mkprocedure_declaration
           1 101 nil nil
             (D_Sequence
                (D_Object_declaration
                   {|
                     declaration_astnum := 3;
                     object_name := 4;
                     object_nominal_subtype :=  5;
                     initialization_expression := Some (E_Literal 6 (Integer_Literal(34)))
                   |}
                )
                (D_Object_declaration
                   {|
                     declaration_astnum := 4;
                     object_name := 5;
                     object_nominal_subtype :=  5;
                     initialization_expression := Some (E_Literal 6 (Integer_Literal(37)))
                   |}
                )
             )
             (S_Sequence 13
                (S_Assignment 14 5
                              (E_Binary_Operation 9 Plus
                                                  (E_Identifier 10 5)
                                                  (E_Identifier 10 4)))
                (S_Assignment
                   12
                   102
                   (E_Binary_Operation 9 Multiply
                                       (E_Identifier 10 5)
                                       (E_Literal 8 (Integer_Literal(2))))))).

Definition sto3:store := (101,Procedure proc2) :: (102, Value (Int(77))) :: nil.

Definition sto4:store := (101,Procedure proc2) :: (102, Value (Int(142)))  :: nil.



Lemma essai2: eval_stmt (sto3::nil) (S_ProcCall 13 101 nil) (Normal (sto4::nil)).
Proof.
  eapply eval_S_Proc; try now (simpl; eauto).
  - simpl.
    constructor.
  - constructor 1.
    reflexivity.
  - 
(*     instantiate (1:= ((5, Value (Int 37))::(4, Value (Int 34))::s3)). *)
    unfold sto3, sto4, proc1.
    simpl.
    econstructor 4;simpl.
    + econstructor 2;simpl.
      * econstructor;eauto.
      * reflexivity.
      * constructor.
        simpl.
        reflexivity.
    + econstructor 2;simpl.
      * econstructor;eauto.
      * reflexivity.
      * constructor.
        simpl.
        reflexivity.
  - simpl.
    + { econstructor.
        - econstructor.
          + econstructor.
            * econstructor.
              simpl.
              eauto.
            * constructor.
              simpl.
              eauto.
            * constructor.
              vm_compute.
              reflexivity.
            * econstructor.
              simpl.
              eauto.
          + simpl.
            reflexivity.
        - econstructor.
          + econstructor.
            * econstructor.
              simpl.
              eauto.
            * econstructor.
              simpl.
              eauto.
            * econstructor.
              vm_compute.
              reflexivity.
            * econstructor.
            simpl.
            eauto.
        + simpl.
          rewrite app_nil_r.
          reflexivity. }
  - simpl.
    constructor 1.
Qed.


End ExampleProcedures.
(* END EXAMPLE *)  

(** ** Functional Semantics of expressions *)

(** for relational semantics of expression and statement, we also 
    provide its corresponding version of functional semantics, and 
    prove that they are semantics equivalent;
    relational semantics encode the formal semantics rules, while
    functional semantics is useful to familiarize oneself with the 
    SPARK 2014 semantics, and validate it experimentally by testing, 
    and it also helps to fix the program if the program exhibits 
    undefined behavior;
    
    Bisimulation between relational and functional semantics are
    proved for the following pairs of evaluations: 
    
    - f_eval_binexpr <-> eval_binexpr;
    
    - f_eval_unaryexpr <-> eval_unaryexpr;
    
    - f_eval_expr <-> eval_expr;

    - f_eval_stmt <-> eval_stmt;
*)

(** *** semantic of operators *)

(** interpret the binary operation for each binary operator *)
Definition f_eval_bin_expr (op: binary_operator) (v1: value) (v2: value): Return value :=
    match op with
    | Equal => Val.eq v1 v2
    | Not_Equal => Val.ne v1 v2
    | Greater_Than => Val.gt v1 v2
    | Greater_Than_Or_Equal => Val.ge v1 v2
    | Less_Than => Val.lt v1 v2
    | Less_Than_Or_Equal => Val.le v1 v2
    | And => Val.and v1 v2
    | Or => Val.or v1 v2
    | Plus => Val.add v1 v2
    | Minus => Val.sub v1 v2
    | Multiply => Val.mul v1 v2
    | Divide => Val.div v1 v2
    end.

(** interpret the unary operation *)
Definition f_eval_unary_expr (op: unary_operator) (v: value): Return value :=
    match op with
    | Not => Val.not v
    | Unary_Plus => Val.unary_add v
    end.

(** *** Expression semantics *)

(** in functional semantics for expression, it returns either a
    normal value or a run time error or go abnormal, the run time 
    checks (for example, division by zero check) are encoded inside 
    the semantics; *)
Function f_eval_expr (s: stack) (e: expression): Return value :=
    match e with
    | E_Literal _ v => Normal (eval_literal v)
    | E_Identifier _ x =>
        match (fetchG x s) with
        | Some (Value v) => Normal v
        | _ => Abnormal (* None or not a value *)
        end
    | E_Binary_Operation _ op e1 e2 =>
        match f_eval_expr s e1 with
        | Normal v1 => 
            match f_eval_expr s e2 with
            | Normal v2 => 
                match f_do_check op v1 v2 with
                | Some true => f_eval_bin_expr op v1 v2
                | Some false => Run_Time_Error
                | _ => Abnormal
                end
            | Run_Time_Error => Run_Time_Error
            | Abnormal => Abnormal
            | Unterminated => Unterminated
            end
        | Run_Time_Error => Run_Time_Error
        | Abnormal => Abnormal
        | Unterminated => Unterminated
        end   
    | E_Unary_Operation _ op e => 
        match f_eval_expr s e with
        | Normal v => f_eval_unary_expr op v
        | Run_Time_Error => Run_Time_Error
        | Abnormal => Abnormal
        | Unterminated => Unterminated
        end
    end.

(** ** Functional Statement semantics *)


(** *** Functional manipulation of the stack for procedure call and
    retrun *)

(** functional version of Copy_out
  [copy_out prefx params lexp s'] returns s' updated in the following
  way: for each param in params that is Out, pick the correponding
  variable name in lexp and update s' with the value of the param that
  is stored in prefix. *)
Function copy_out (prefx:store) (params: list parameter_specification)
         (lexp:list expression) (s: stack) {struct params}:  Return stack :=
  match params, lexp with
    | nil , nil => Normal s
    | (prm::params') , (e::lexp') =>
      match prm.(parameter_mode) with
         | Out =>
           match e with
             | E_Identifier _ x =>
               match (fetch (prm.(parameter_name)) prefx) with
                   Some v =>
                   match updateG s x v with
                     | Some s' => copy_out prefx params' lexp' s'
                     | None => Abnormal
                   end
                 | None => Abnormal
               end
             | _ => Abnormal
           end
         | In => copy_out prefx params' lexp' s
         | _ => Abnormal
       end
    | _ , _ => Abnormal
  end.

(** Functional version of Copy_in.
   [copy_in s lparams lexp] returns the prefix to push on the stack
   before evaluationg procedure body (i.e. declaration block +
   statement). "Out" parameters values are copied into there output
   variables (stored in lexp). *)
Function copy_in (s:stack) lparams lexp: Return store :=
  match lparams,lexp with
  | (prm :: lparams') , (exp:: lexp') =>
    match prm.(parameter_mode) with
      | Out => if is_var exp
               then match copy_in s lparams' lexp' with
                      | Normal res => Normal ((prm.(parameter_name), Undefined) :: res)
                      | res => res
                    end
               else Abnormal
      | In =>
        let v := f_eval_expr s exp in
        match v with
          | Normal v' =>
            match copy_in s lparams' lexp' with
              | Normal res => Normal ((prm.(parameter_name), Value v') :: res)
              | res => res
            end
          | Run_Time_Error => Run_Time_Error
          | Abnormal => Abnormal
          | Unterminated => Unterminated
        end
      | In_Out => Abnormal (* not yet implemented *)
    end
  | nil , nil => Normal nil
  | _ , _ => Abnormal
  end.

(** *** functional semantic of declarations *)

Function f_eval_decl (s: stack) (sto:store) (c: declaration) {struct c}: Return store :=
  match c with
    | D_Object_declaration d =>
      match d.(initialization_expression) with
        | Some e =>
          match f_eval_expr (sto::s) e with
            | Run_Time_Error => Run_Time_Error
            | Normal v =>
              (Normal ((d.(object_name), Value v)::sto))
            | Abnormal => Abnormal
            | Unterminated => Unterminated
          end
        | None => (Normal ((d.(object_name), Undefined) :: sto))
      end
    | D_Sequence dcl1 dcl2 =>
      match f_eval_decl s sto dcl1 with
        | Normal s' => f_eval_decl s s' dcl2
        | err => err
      end
    | D_Procedure_declaration pbody =>
      Normal((procedure_name pbody,Procedure pbody)::sto)
  end.

(** *** functional semantic of statements *)

(** 
   in the functional semantics for statement, 'k' denotes the execution 
   steps, whenever it reaches 0, an untermination state is returned;
   otherwise, it returns either a normal state, or a run time error 
   or an abnormal state; run time checks (for example, division by 
   zero check) are encoded inside the functional semantics;
*)





Function f_eval_stmt k (s: stack) (c: statement) {struct k}: Return stack := 
  match k with
  | 0 => Unterminated
  | S k' => 
    match c with
    | S_Assignment ast_num x e =>
        match f_eval_expr s e with
        | Normal v => 
            match updateG s x (Value v) with
            | Some s1 => Normal s1
            | None => Abnormal
            end
        | Run_Time_Error => Run_Time_Error
        | Abnormal => Abnormal
        | Unterminated => Unterminated
        end
    | S_Sequence ast_num c1 c2 =>
        match f_eval_stmt k' s c1 with
        | Normal s1 => f_eval_stmt k' s1 c2
        | Run_Time_Error => Run_Time_Error
        | Unterminated => Unterminated
        | Abnormal => Abnormal
        end
    | S_If ast_num b c =>
        match f_eval_expr s b with
        | Normal (Bool true) => f_eval_stmt k' s c
        | Normal (Bool false) => Normal s
        | Run_Time_Error => Run_Time_Error
        | Unterminated => Unterminated
        | _ => Abnormal
        end
    | S_While_Loop ast_num b c => 
        match f_eval_expr s b with
        | Normal (Bool true) => 
            match f_eval_stmt k' s c with
            | Normal s1 => f_eval_stmt k' s1 (S_While_Loop ast_num b c)
            | Run_Time_Error => Run_Time_Error
            | Unterminated => Unterminated
            | Abnormal => Abnormal
            end
        | Normal (Bool false) => Normal s
        | Run_Time_Error => Run_Time_Error
        | Unterminated => Unterminated
        | _ => Abnormal
        end
    | S_ProcCall ast_num pbname lexp =>
      match fetchG pbname s with
        | Some (Procedure pb) => 
          match copy_in s (procedure_parameter_profile pb) lexp with
            | Normal prefx => 
              match cut_until s pbname with
                | Some (s_forget, s_called) =>
                  match f_eval_decl s_called prefx (procedure_declarative_part pb) with
                    | Normal s2 =>
                      match f_eval_stmt k' (s2::s_called) (procedure_statements pb) with
                        | Normal (frame::s') =>
                          match split1 _ (List.length frame - List.length prefx) frame with
                            | Some (slocal,prefx') =>
                              (copy_out prefx' (procedure_parameter_profile pb) lexp (s_forget++s'))
                            | None => Abnormal (* erronous store size *)
                          end
                        | Run_Time_Error => Run_Time_Error
                        | _ => Abnormal (* erronous stack size or abnormal result *)
                      end
                    | Run_Time_Error => Run_Time_Error
                    | _ => Abnormal
                  end
                | None => Abnormal (* procedure doesn't exist *)
              end
            (* left and right are not of the same type (return_state
               store) and (return_state stack) *)
            | Run_Time_Error => Run_Time_Error
            | Abnormal => Abnormal
            | Unterminated => Unterminated
          end
        | _ => (* None or non-procedure *) Abnormal
      end
    end
  end.

(* My renaming heuristic. Not perfect. *)
Ltac semantic_rename_hyp th :=
  match th with
    | (do_check _ _ _ _) => fresh "hdo_check"
    | (eval_expr _ _ Run_Time_Error) => fresh "heval_expr_rte"
    | (eval_expr _ _ _) => fresh "heval_expr"
    | (eval_decl _ _ _ _) => fresh "heval_decl"
    | (eval_stmt _ _ _) => fresh "heval_stmt"
    | (eval_bin_expr _ _ _ _) => fresh "heval_bin_expr"
    | (eval_unary_expr _ _ _) => fresh "heval_unary_expr"
    | (eval_literal _ = _) => fresh "heqeval_literal"
    | (updateG _ _ _ = _) => fresh "hupdateG"
    | (update _ _ _ = _) => fresh "hupdate"
    | (fetchG _ _ = _) => fresh "heqfetchG"
    | (fetch _ _ = _) => fresh "heqfetch"
    | (Copy_in _ _ _ _) => fresh "hCopy_in"
    | (Cut_until _ _ _ _) => fresh "hCut_until"
    | (f_eval_expr _ _ = Run_Time_Error) => fresh "heqeval_expr_rte"
    | (f_eval_expr _ _ = _) => fresh "heqeval_expr"
    | (f_eval_decl _ _ _ = _) => fresh "heqeval_decl"
    | (f_eval_stmt _ _ _ = _ ) => fresh "heqeval_stmt"
    | (f_eval_bin_expr _ _ _ = _) => fresh "heqeval_bin_expr"
    | (f_do_check _ _ _ = _) => fresh "heqdo_check"
    | (stack_eq_length _ _) => fresh "hstack_eq_length"
    | _ => default_rename_hyp th
  end.
Ltac rename_hyp ::= semantic_rename_hyp.

Lemma eval_expr_unique: forall s e v1 v2,
    eval_expr s e v1 ->
    eval_expr s e v2 ->
    v1 = v2.
Proof.
  intros s e v1 v2 hv1.
  revert v2.
  !induction hv1;!intros.
  - subst.
    !inversion heval_expr.
    reflexivity.
  - !inversion heval_expr; !intros.
    Rinversion fetchG.    
  - !inversion heval_expr;auto;!intros.
    apply IHhv1 in heval_expr1.
    discriminate.
  - !inversion heval_expr0; !intros ; auto.
    apply IHhv1_2 in heval_expr1.
    discriminate.
  - !inversion heval_expr1;auto;!intros.
    apply f_do_check_complete in hdo_check.
    apply f_do_check_complete in hdo_check0.
    apply IHhv1_2 in heval_expr2.
    apply IHhv1_1 in heval_expr3.
    injection heval_expr2.
    injection heval_expr3.
    intros; subst.
    rewrite hdo_check in hdo_check0.
    discriminate.
  - !inversion heval_expr1;!intros.
    + apply IHhv1_1 in heval_expr_rte.
      discriminate.
    + apply IHhv1_2 in heval_expr_rte.
      discriminate.
    + apply f_do_check_complete in hdo_check0.
      apply f_do_check_complete in hdo_check.
      apply IHhv1_1 in heval_expr3.
      apply IHhv1_2 in heval_expr2.
      injection heval_expr3.
      injection heval_expr2.
      intros ; subst.
      rewrite hdo_check in hdo_check0.
      discriminate.
    + apply IHhv1_1 in heval_expr3.
      apply IHhv1_2 in heval_expr2.
      injection heval_expr3.
      injection heval_expr2.
      intros ;subst.
      rewrite (eval_bin_unique _ _ _ _ _ heval_bin_expr heval_bin_expr0) .
      reflexivity.
  - !inversion heval_expr;auto;!intros.
    apply IHhv1 in heval_expr0.
    discriminate.
  - !inversion heval_expr;!intros.
    + apply IHhv1 in heval_expr_rte.
      discriminate.
    + apply IHhv1 in heval_expr0.
      injection heval_expr0.
      intros ;subst.
      rewrite (eval_unary_unique _ _ _ _ heval_unary_expr0 heval_unary_expr) .
      reflexivity.
Qed.    


(** 
    for any expression e evaluated under the state s, if it can be 
    evaluated to a value v with respect to the relational semantics 
    eval_expr, then the result value v should be either a normal 
    value or a run time error;
*)
Lemma eval_expr_state : forall s e v,
        eval_expr s e v -> (* v should be either a normal value or a run time error *)
            (exists v0, v = Normal v0) \/ v = Run_Time_Error.
Proof.
    intros s e v h.
    induction h;
    try match goal with
    | [ |- (exists v, Normal ?v1 = Normal v) \/ _ ]
      => left; exists v1; reflexivity
    | [ |- context [ _ \/ ?A = ?A ] ] => right; reflexivity
    end; auto.
Qed.

(** 
    for any statement c starting from the initial state s, if it 
    terminates in a state s' with respect to the relational semantics 
    eval_stmt, then the result state s' should be either a normal 
    state or a run time error. In relational semantics eval_stmt, 
    all statements that can go abnormal are excluded;
*)
Lemma eval_stmt_state : forall s c s',
        eval_stmt s c s' -> (* s' is either a normal state or a run time error *)
            (exists v, s' = Normal v) \/ s' = Run_Time_Error.
Proof.
    intros s c s' h.
    induction h;
    try match goal with
    | [ |- (exists v, Normal ?v1 = Normal v) \/ _ ] => left; exists v1; reflexivity
    | [ |- context [ _ \/ ?A = ?A ] ] => right; reflexivity
    end; auto.
Qed.

(** * Bisimulation Between Relational And Functional Semantics *)

(** bisimulation proof between f_eval_binexpr and eval_binexpr:
    - f_eval_bin_expr_correct
    - f_eval_bin_expr_complete
*)
Lemma f_eval_bin_expr_correct: forall op v1 v2 v,
    f_eval_bin_expr op v1 v2 = Normal v ->
    eval_bin_expr op v1 v2 v.
Proof.
    intros op v1 v2 v h1.
    destruct op;
    match goal with 
    |[|- eval_bin_expr Divide _ _ _] => idtac
    |[|- eval_bin_expr ?op _ _ _] =>
        destruct v1, v2;
        simpl in h1; inversion h1; subst;
        constructor; auto
    end.
    destruct v1, v2; simpl in h1; inversion h1.
    constructor.
    remember (Zeq_bool n0 0) as x.
    reflexivity.
Qed.

Lemma f_eval_bin_expr_complete: forall op v1 v2 v,
    eval_bin_expr op v1 v2 v ->
    f_eval_bin_expr op v1 v2 = Normal v.
Proof.
    intros op v1 v2 v h1.
    induction h1;
    rewrite <- H;
    simpl; auto.
Qed.

(** bisimulation proof between f_eval_unaryexpr and eval_unaryexpr: 
    - f_eval_unary_expr_correct
    - f_eval_unary_expr_complete
*)
Lemma f_eval_unary_expr_correct: forall op v v',
    f_eval_unary_expr op v = Normal v' ->
    eval_unary_expr op v v'.
Proof.
  intros op v v' heq.
  !destruct op ; simpl in heq.
  - destruct v; inversion heq; subst.
    constructor; auto.
  - destruct v;destruct v';simpl in *;try discriminate.
    injection heq.
    intro.
    subst.
    constructor 2.      
Qed.

Lemma f_eval_unary_expr_complete: forall op v v',
    eval_unary_expr op v v' ->
    f_eval_unary_expr op v = Normal v'.
Proof.
  intros op v v' h1.
  induction h1;simpl;subst;auto.
Qed.

(** ** Bisimulation between f_eval_expr and eval_expr for expression Semantics *)
(** a help lemma to prove the theorem: f_eval_expr_correct *)
Lemma f_eval_expr_correct1 : forall s e v,
                        f_eval_expr s e = Normal v ->
                            eval_expr s e (Normal v).
Proof.
  intros s e.
  !!(functional induction (f_eval_expr s e); intros v0 h1; try inverts h1 as; subst).
  - constructor;
    reflexivity.
  - constructor;
    assumption.
  - specialize (IHr _ heqeval_expr0).
    specialize (IHr0 _ heqeval_expr).
    introv h.
    rewrite h.
    econstructor.
    + exact IHr.
    + exact IHr0.
    + apply f_do_check_correct.
      auto.
    + apply f_eval_bin_expr_correct; 
      auto.
  - specialize (IHr _ heqeval_expr).
    introv h.
    rewrite h.
    econstructor. 
    + exact IHr.
    + destruct op. 
      * simpl in h. 
        destruct v; inversion h; subst.
        constructor; auto.
      * simpl in h. 
        destruct v; inversion h; subst.
        constructor; auto.
Qed.


(** another help lemma to prove the theorem: f_eval_expr_correct *)
Lemma f_eval_expr_correct2 : forall s e,
                        f_eval_expr s e = Run_Time_Error ->
                            eval_expr s e Run_Time_Error.
Proof.
    intros s e.
    (!! functional induction (f_eval_expr s e)); intro h;inversion h;simpl. 
  - destruct op, v1, v2; simpl in h; inversion h.
  - specialize (f_eval_expr_correct1 _ _ _ heqeval_expr0); intros hz1.
    specialize (f_eval_expr_correct1 _ _ _ heqeval_expr); intros hz2.
    eapply eval_E_Binary_Operation3.
    apply hz1. apply hz2.
    apply f_do_check_correct; auto.
  - specialize (f_eval_expr_correct1 _ _ _ heqeval_expr); intros hz1.
    specialize (IHr0 heqeval_expr_rte).
    eapply eval_E_Binary_Operation2 with v1; auto.
  - specialize (IHr heqeval_expr_rte).
    constructor; assumption.
  - destruct op;
    destruct v; inversion h. 
  - specialize (IHr heqeval_expr_rte).
    constructor; assumption.
Qed.

(** *** f_eval_expr_correct *)
(** 
    for an expression e evaluated under the state s with respect to
    the functional semantics f_eval_expr, whenever it returns a 
    normal value v or terminates in a run time error, 
    the relation between s, e and evaluation result should also be 
    satisfied with respect to the relational semantics 'eval_expr';
*)
Theorem f_eval_expr_correct : forall s e v,
                        (f_eval_expr s e = Normal v ->
                            eval_expr s e (Normal v)) /\
                        (f_eval_expr s e = Run_Time_Error ->
                            eval_expr s e Run_Time_Error).
Proof.
    split.
  - apply f_eval_expr_correct1.
  - apply f_eval_expr_correct2.
Qed.


(** *** f_eval_expr_complete *)
(** 
   for any expression e, if it can be evaluated to a value v under
   state s with respect to the relational semantics 'eval_expr', 
   then when we evalute e under the same state s in functional
   semantics 'f_eval_expr', it should return the same result v;
*)
Theorem f_eval_expr_complete : forall e s v,  
                        eval_expr e s v -> 
                            (f_eval_expr e s) = v.
Proof.
    intros e s v h.
    !induction h; simpl; !intros;
    repeat match goal with
    | h: fetchG _ _ = _  |- _ => progress rewrite h
    | h: f_eval_expr _ _ = _ |- _ => progress rewrite h
    end;auto.
  - rewrite heqeval_literal; reflexivity.
  - specialize (f_do_check_complete _ _ _ _ hdo_check); intros hz1.
    rewrite hz1.
    reflexivity.
  - !destruct v1; !destruct v2;
    !destruct op;
    !inversion heval_bin_expr; subst; simpl; auto.
    + (* overflow check for Plus *)
      !inversion hdo_check; !intros; subst.
      * rewrite heq; auto.
      * rm_false_hyp.
    + (* overflow check for Minus *)
      !inversion hdo_check;!intros; subst.
      * rewrite heq; auto.
      * rm_false_hyp.
    + (* overflow check for Multiply *)
      !inversion hdo_check;!intros; subst.
      * inversion heq; subst.
        rewrite H0; auto.
      * rm_false_hyp.
    + (* both division by zero check and overflow check *)
      !inversion hdo_check;!intros; subst.
      * inversion heq; subst.
        rewrite H0; auto.
      * rm_false_hyp.
  - destruct op.
    + !inversion heval_unary_expr.
      auto.
    + !inversion heval_unary_expr.
      auto.
Qed.






Ltac apply_inv :=
  try discriminate; try Rdiscriminate;
  match goal with
    | H:Normal _ = Normal _ |- _ => inversion H;clear H;subst 
    | H:update _ _ (Value _) = _ |- _ => rewrite H
    | H:updateG _ _ (Value _) = _ |- _ => rewrite H
    | H:f_eval_stmt _ _ _ = _ |- _ => rewrite H
    | H:f_eval_expr _ _ = _ |- _ => rewrite H
    | H:f_eval_decl _ _ _ = _ |- _ => rewrite H
    | H:copy_out _ _ _ _ = _ |- _ => rewrite H
    | H:copy_in _ _ _ = _ |- _ => rewrite H
    | H:fetch _ _ = _ |- _ => rewrite H
    | H:fetchG _ _ = _ |- _ => rewrite H
    | H:split2 _ _ _ = _ |- _ => rewrite H
    | H:split1 _ _ _ = _ |- _ => rewrite H
    | H:cut_until _ _ = _ |- _ => rewrite H
  end;subst;simpl;auto.

Ltac invle := match goal with
    | H: (S _ <= _)%nat |- _ => (inversion H; clear H; subst; simpl)
  end.

(** a help lemma to prove the theorem: 'f_eval_stmt_complete',
    it means that: for any statement c, starting from initial state s, 
    if it terminates in a normal state s' within k execution steps, 
    then for any k' greater and equal than k, it should also terminate 
    in the same state s';
*)
Lemma f_eval_stmt_fixpoint: forall k s c s', 
        f_eval_stmt k s c = Normal s' ->
        forall k':nat, (k <= k')%nat -> 
            f_eval_stmt k' s c = Normal s'.
Proof.
    intros k s c.
    rename_after (fun _ => functional induction (f_eval_stmt k s c); simpl; intros; subst; simpl; auto;
    repeat progress apply_inv) c.
  - invle; repeat apply_inv.
  - invle.
    + repeat apply_inv.
    + rewrite (IHr _ heqeval_stmt0);auto with arith.
  - invle; repeat apply_inv. rewrite (IHr _ heqeval_stmt);auto with arith.
  - invle; repeat apply_inv.
  - invle; repeat apply_inv. rewrite (IHr _ heqeval_stmt0); auto with arith.
  - invle; repeat apply_inv.
  - invle; repeat apply_inv.
    rewrite (IHr _ heqeval_stmt).
    repeat apply_inv.
    auto with arith.
Qed.

(** another help lemma to prove the theorem: 'f_eval_stmt_complete' *)
Lemma f_eval_stmt_fixpoint_E: forall k s p, 
        f_eval_stmt k s p = Run_Time_Error ->
        forall k':nat, (k <= k')%nat -> 
            f_eval_stmt k' s p = Run_Time_Error.
Proof.
    intros k s p.
    rename_after (fun _ => functional induction (f_eval_stmt k s p)
                  ; simpl; intros; subst; simpl; auto;
                  repeat progress apply_inv) p.
  - invle;
    apply_inv.
  - invle;
    repeat apply_inv.
    rewrite (f_eval_stmt_fixpoint _ _ _ _ heqeval_stmt0); auto with arith.
  - invle;
    repeat apply_inv.
    specialize (IHr heqeval_stmt). 
    rewrite IHr; auto with arith. 
  - invle; 
    repeat apply_inv.
    rewrite IHr; auto with arith.
  - invle;
    repeat apply_inv.
  - invle; 
    repeat apply_inv. 
    rewrite (f_eval_stmt_fixpoint _ _ _ _ heqeval_stmt0); auto with arith.
  - invle; 
    repeat apply_inv.
    rewrite (IHr heqeval_stmt); auto with arith.    
  - invle; 
    repeat apply_inv.   
  - invle; repeat apply_inv.
    rewrite (f_eval_stmt_fixpoint _ _ _ _ heqeval_stmt); auto with arith.
    rewrite heq0.
    assumption.
  - invle; repeat apply_inv.
    rewrite  (IHr heqeval_stmt m);auto with arith.
  - invle; repeat apply_inv.
  - invle; repeat apply_inv.
Qed.



Ltac rm_eval_expr :=
  match goal with 
    | [ h: eval_expr ?s ?b ?X, h': f_eval_expr ?s ?b = ?X |- _ ] => clear h
    | [ h: eval_expr ?s ?b ?X, h': ?X = f_eval_expr ?s ?b |- _ ] => clear h; symmetry in h'
    | [ h: eval_expr ?s ?b ?X |- _ ] => apply f_eval_expr_complete in h
  end; auto.


Lemma copy_in_correct:
  forall s prm lexp prefx,
    copy_in s prm lexp = (Normal prefx) <->  Copy_in s prm lexp (Normal prefx).
Proof.
  intros s prm lexp.
  rename_after
    (fun _ =>
       functional induction copy_in s prm lexp;intros;split;simpl in *;intro heq
     ; try (inversion heq;subst;clear heq)
     ; repeat rm_eval_expr
     ; try repeat progress match goal with (* Rewrite induction hyp if you can *)
                             | H: (forall _, ?X = _ <-> _)  |- _ =>
                               rewrite <- H in *
                           end
     ; try (now repeat progress
                first [ Rdiscriminate
                      | Rinversion copy_in;auto
                      | Rinversion f_eval_expr;auto ])) lexp.
  - inversion_is_var heq0.
    econstructor 2.
    + apply IHr;auto.
    + assumption.

  - apply Copy_in_cons_in.
    + apply IHr.
      assumption.
    + assumption.
    + apply f_eval_expr_correct1.
      assumption.
  - constructor 1.
Qed.



Lemma copy_in_correct2:
  forall s prm lexp,
    copy_in s prm lexp = Run_Time_Error <->  Copy_in s prm lexp Run_Time_Error.
Proof.
  intros s prm lexp.
  rename_after
    (fun _ => functional induction copy_in s prm lexp;intros;split;simpl in *;intro heq
     ; try (inversion heq;subst;clear heq)
     ; repeat try rm_eval_expr
     ; try repeat progress (* Rewrite with induction hyp as much as we can *)
           match goal with
             | H: (?X = _ <-> _)  |- _ =>
               rewrite <- H in *
           end
     ; try (now repeat progress
                first [ Rdiscriminate
                      | Rinversion copy_in;auto
                      | Rinversion f_eval_expr;auto ])) lexp.
  - inversion_is_var heq0.
    rewrite heq.
    econstructor;auto.
    rewrite <- IHr.
    assumption.
  - rewrite heq.
    apply Copy_in_cons_in_rte2 with (v:=v');auto.
    + rewrite <- IHr.
      assumption.
    + apply f_eval_expr_correct1.
      assumption.
  - apply Copy_in_cons_in_rte1;auto.
    apply f_eval_expr_correct2.
    assumption.
Qed.

Lemma Copy_out_stack_eq_length :
  forall prefx prm lexp s s',
    Copy_out prefx prm lexp s s'
    -> stack_eq_length s s'.
Proof.
  intros prefx prm lexp s s' H.
  induction H;auto.
  - apply stack_eq_length_refl.
    reflexivity.
  - transitivity  σ'.
    + eapply updateG_stack_eq_length;eauto.
    + assumption.
Qed.

Lemma Copy_out_length :
  forall prefx prm lexp s s',
    Copy_out prefx prm lexp s s'
    -> List.length s = List.length s'.
Proof.
  intros prefx prm lexp s s' H.
  induction H;auto.
  transitivity (List.length σ');auto.
  eapply updateG_length;eauto.
Qed.



Lemma copy_out_no_rte:
  forall prefx lprm lexp s,
    ~ copy_out prefx lprm lexp s = Run_Time_Error.
Proof.
  intros prefx lprm lexp s.
  functional induction copy_out prefx lprm lexp s;try assumption;try discriminate.
Qed.


Lemma copy_out_correct:
  forall prefx s (prm:list parameter_specification) lexp x,
    copy_out prefx prm lexp s = Normal x <-> Copy_out prefx prm lexp s x.
Proof.
  intros prefx s prm lexp.
  rename_after
    (fun _ =>
       functional induction copy_out prefx prm lexp s;intros;split;simpl in *;intro heq
     ; try (now (inversion heq;subst;clear heq);auto;try now (econstructor;eauto))) lexp.
  - apply Copy_out_cons_out with (σ':=s') (v:=v)(id:=parameter_name prm);auto.
    apply IHr.
    assumption.
  - !inversion heq;!intros.
    + Rinversion fetch.
      Rinversion updateG. 
      apply IHr;assumption.
    + Rdiscriminate.
  - !inversion heq;!intros.
    + Rinversion fetch.
      Rdiscriminate.
    + Rdiscriminate.
  - !inversion heq; !intros.
    + Rdiscriminate.
    + Rdiscriminate.
  - !inversion heq; !intros.
    + contradiction.
    + Rdiscriminate.
  - constructor 3;auto.
    apply IHr.
    assumption.
  - !inversion heq;!intros.
    + Rdiscriminate.
    + apply IHr.
      assumption.
  - !inversion heq;!intros.
    + rewrite heq0 in y.
      contradiction.
    + rewrite heq0 in y.
      contradiction.
Qed.





Lemma eval_decl_store_length:
  forall s sto s' decl,
    eval_decl s sto decl s'
    -> forall st, s' = Normal st
                  -> exists prfx, st = prfx ++ sto.
Proof.
  intros s sto s' decl h.
  !induction h;intros st heq';!inversion heq';subst.
  - exists ((object_name d, Value v)::nil).
    simpl.
    reflexivity.
  - exists ((object_name d, Undefined)::nil);simpl.
    reflexivity.
  - destruct (IHh2 st).
    { reflexivity. }
    destruct (IHh1 s').
    { reflexivity. }
    subst.
    exists (x ++ x0).
    apply app_assoc.
  - exists ((procedure_name pbody, Procedure pbody)::nil);simpl.
    reflexivity.
Qed.


Lemma eval_stmt_store_length:
  forall s s' stm,    
    eval_stmt s stm s'
    -> forall st, s' = Normal st
                  -> stack_eq_length s st.
Proof.
  intros s s' stm H.
  (*    !! (induction H;intros st heq';inversion heq';clear heq'; subst;auto). *)
  (!!induction H; intros st heq'; inversion heq';clear heq'; subst;auto).
  - apply updateG_stack_eq_length in hupdateG.
    assumption.
  - apply stack_eq_length_trans with s1.
    + apply IHeval_stmt1.
      reflexivity.
    + apply IHeval_stmt2.
      reflexivity.
  - apply stack_eq_length_refl.
    reflexivity.
  - apply stack_eq_length_trans with s1.
    + apply IHeval_stmt1.
      reflexivity.
    + apply IHeval_stmt2.
      reflexivity.
  - apply stack_eq_length_refl.
    reflexivity.
  - generalize (Cut_until_def _ _ _ _ hCut_until).
    intros hcutin.
    subst.
    specialize (IHeval_stmt ((slocal ++ prefix') :: s') eq_refl).
    !inversion IHeval_stmt;!intros.
    rewrite hstack_eq_length.
    eapply Copy_out_stack_eq_length;eauto.
Qed.

Lemma f_eval_decl_correct :
  forall s sto d s',
    f_eval_decl s sto d = Normal s' ->
    eval_decl s sto d (Normal s').
Proof.
  intros s sto d.
  functional induction f_eval_decl s sto d;simpl;intros;try discriminate
  ; try match goal with
        | H: Normal _ = Normal _ |- _ =>
          inversion H;subst;clear H
      end;try now( (econstructor;eauto;try apply f_eval_expr_correct1;auto)).
  - rewrite H in y.
    contradiction.
Qed.

Lemma f_eval_decl_correct2 :
  forall s sto d,
    f_eval_decl s sto d = Run_Time_Error ->
    eval_decl s sto d Run_Time_Error.
Proof.
  intros s sto d.
  functional induction f_eval_decl s sto d;simpl;intros;try discriminate;
  try match goal with
        | H: Normal _ = Run_Time_Error |- _ =>
          inversion H;subst;clear H
      end;try now( (econstructor;eauto);try apply f_eval_expr_correct2;auto).
  
  eapply eval_decl_Seq_err2 with s';auto.
  apply f_eval_decl_correct.
  assumption.
Qed.

Ltac use_determinism :=
  match goal with
    | H : ?X = ?X |- _ => clear H
    | H: None = ?y, H': ?y = Some ?z |- _ => rewrite H' in H; !invclear H
    | H: Some ?z = ?y, H': ?y = None |- _ => rewrite H' in H; !invclear H
    | H: Some ?x = ?y, H': ?y = Some ?z |- _ => rewrite H' in H; !invclear H
    | H : eval_expr ?s ?e ?X,
          H': f_eval_expr ?s ?e = ?Y |- _ => rewrite (f_eval_expr_complete s e X H) in H'
    | H:  eval_expr ?s ?e ?X,
          H': eval_expr ?s ?e ?Y |- _ => apply (f_eval_expr_complete s e X) in H
         ;apply (f_eval_expr_complete s e) in H'
    | H : f_eval_expr ?s ?e = ?X,
          H': f_eval_expr ?s ?e = ?Y |- _ => rewrite H in H'; !invclear H'
    | H : (Normal ?v) = (Normal ?v') |- _ => !invclear H
  end.

Ltac crush := repeat progress use_determinism;try reflexivity;try discriminate.


Lemma f_eval_decl_complete :
  forall d sto s s',
    eval_decl s sto d s' ->
    f_eval_decl s sto d = s'.
Proof.
  intros d sto s.
  (!!functional induction f_eval_decl s sto d);simpl;!intros;try discriminate;crush;
  try now (!inversion heval_decl;!intros;crush).
  - !inversion heval_decl;!intros.
    + apply IHr in heval_decl1.
      Rinversion f_eval_decl.
    + apply IHr in heval_decl0.
      Rinversion f_eval_decl.
    + apply IHr in heval_decl1.
      Rinversion f_eval_decl.
  - !inversion heval_decl;!intros.
    + apply IHr in heval_decl1.
      Rinversion f_eval_decl.
    + apply IHr in heval_decl0.
      assumption.
    + apply IHr in heval_decl1.
      rewrite heval_decl1 in y.
      contradiction.
Qed.


(** ** Bisimulation between f_eval_stmt and eval_stmt for statement semantics *)


Ltac rm_f_eval_expr :=
  match goal with 
    | [ h: f_eval_expr ?s ?b = Run_Time_Error |- _ ] => 
      specialize (f_eval_expr_correct2 _ _ h);
        !intros
    | [ h: f_eval_expr ?s ?b = Normal ?v |- _ ] => 
      specialize (f_eval_expr_correct1 _ _ _ h);
        !intros
  end; auto.



(** a help lemma to prove the theorem: 'f_eval_stmt_complete' *)
Lemma f_eval_stmt_correct1 : forall k s p s',
        f_eval_stmt k s p = Normal s' ->
          eval_stmt s p (Normal s').
Proof.
    intros k s p.
    !!(functional induction (f_eval_stmt k s p);
       intros; try inversion H; subst).
  - (* S_Assignment *)
    econstructor.
    rm_f_eval_expr.
    apply heval_expr.
    assumption.
  - (* S_Sequence *)
    specialize (IHr _ heqeval_stmt1).
    specialize (IHr0 _ heqeval_stmt).
    econstructor.
    apply IHr.
    apply_inv.
  - (* S_If_True *)
    specialize (IHr _ heqeval_stmt).
    econstructor.
    rm_f_eval_expr. 
    apply_inv.
  - (* S_If_False *)
    eapply eval_S_If_False.
    rm_f_eval_expr.
  - (* S_While_Loop_True *)
    specialize (IHr _ heqeval_stmt1).
    specialize (IHr0 _ heqeval_stmt).
    econstructor.
    rm_f_eval_expr.
    apply IHr. 
    apply_inv.
  - (* S_While_Loop_False *)
    eapply eval_S_While_Loop_False.
    rm_f_eval_expr.
  - (* S_ProcCall *)
    clear heq0.
    (* cleaning by going to inductive defs *)
    apply split1_correct in heq1.
    destruct heq1 as [hsplit1 hsplit2].
    rewrite heq.
    subst.
    apply f_eval_decl_correct in heqeval_decl.    
    apply IHr in heqeval_stmt.
    apply copy_in_correct in heq3.
    apply copy_out_correct in heq.
    (* ******* *)
    eapply eval_S_Proc with (s':=s') (prefix':=prefx')(prefix:=prefx)(slocal:=slocal);eauto.
    + apply cut_until_complete1.
      assumption.
    + eapply eval_decl_store_length with (st:=s2) in heqeval_decl;auto.
      destruct heqeval_decl as [slocal' ?].
      subst.
      apply eval_stmt_store_length with (st:=((slocal ++ prefx') :: s')) in heqeval_stmt;auto.
      !invclear heqeval_stmt.
      rewrite <- heq0 in hsplit1.
      setoid_rewrite app_length in heq0.
      setoid_rewrite app_length in hsplit1.
      omega.
Qed.


Ltac rm_f_eval_stmt :=
    match goal with 
    | [ h: f_eval_stmt ?k ?s ?c = Normal ?s1 |- _ ] => 
        specialize (f_eval_stmt_correct1 _ _ _ _ h);
        !intros
    end; auto.

(** a help lemma to prove the theorem: 'f_eval_stmt_complete' *)
Lemma f_eval_stmt_correct2 : forall k s p,
        f_eval_stmt k s p = Run_Time_Error ->
          eval_stmt s p Run_Time_Error.
Proof.
    intros k s p.
    !!(functional induction (f_eval_stmt k s p);intros;try discriminate).
(*     !!(functional induction (f_eval_stmt k s p)); intros H ; try inversion H; subst. *)
  - (* S_Assignment *)
    econstructor.
    rm_f_eval_expr.
  - (* S_Sequence*)
    eapply eval_S_Sequence2.
    + rm_f_eval_stmt.
      eauto.
    + apply IHr0.
      assumption.
  - specialize (IHr heqeval_stmt).
    econstructor.
    assumption.    
  - (* C_If *)
    specialize (IHr heqeval_stmt).
    eapply eval_S_If_True.
    rm_f_eval_expr.
    assumption.
  - eapply eval_S_If .
    rm_f_eval_expr.
  (* S_While_Loop *)
  - eapply eval_S_While_Loop_True2.
    + apply f_eval_expr_correct1.
      assumption.
    + rm_f_eval_stmt.
      eauto.
    + apply IHr0.
      assumption.
  - eapply eval_S_While_Loop_True1;auto.
    rm_f_eval_expr.

  - (* S_While_Loop *)
    apply eval_S_While_Loop.
    rm_f_eval_expr.
  - elim (copy_out_no_rte _ _ _ _ heq).
  - apply eval_S_Proc_rtebody with 
    (prefix:=prefx)
      (s2:=s2)
      (s:=s_called)
      (s_forget:=s_forget)
      (pb:=pb);auto. 
    + apply copy_in_correct.
      assumption.
    + apply cut_until_complete1.
      assumption.
    + apply f_eval_decl_correct.
      assumption.
  - apply eval_S_Proc_rtedecl
    with (prefix:=prefx) (pb:=pb) (s_forget:=s_forget) (s:=s_called)
    ;eauto.
    + apply copy_in_correct.
      assumption.
    + apply cut_until_complete1.
      assumption.
    + eapply f_eval_decl_correct2.
      assumption.
  - eapply eval_S_Proc_rteargs with pb;auto.
    apply copy_in_correct2.
    assumption.
Qed.
    
    

Ltac rm_f_eval :=
    match goal with 
    | [ h: f_eval_expr ?s ?b = Run_Time_Error |- _ ] => specialize (f_eval_expr_correct2 _ _ h); intros hz1
    | [ h: f_eval_expr ?s ?b = Normal ?v |- _ ] => specialize (f_eval_expr_correct1 _ _ _ h); intros hz1   
    | [ h: f_eval_stmt ?k ?s ?c = Run_Time_Error |- _ ] => specialize (f_eval_stmt_correct2 _ _ _ h); intros hz1
    | [ h: f_eval_stmt ?k ?s ?c = Normal ?s1 |- _ ] => specialize (f_eval_stmt_correct1 _ _ _ _ h); intros hz1
    end; auto.

(** *** f_eval_stmt_correct *)
(** 
   for any statement c starting from initial state s, if it returns 
   a normal state s' or terminates in a run time error within k steps
   with respect to the functional semantics 'f_eval_stmt', then the 
   relation between s, c and the resulting state should also be 
   satisfied with respect to the relational semantics 'eval_stmt';
*)
Theorem f_eval_stmt_correct : forall k s c s',
        (f_eval_stmt k s c = Normal s' ->
          eval_stmt s c (Normal s')) /\ 
        (f_eval_stmt k s c = Run_Time_Error ->
          eval_stmt s c Run_Time_Error).
Proof.
    intros.
    split; intros;
    rm_f_eval.
Qed.

(** *** f_eval_stmt_complete *)
(** 
   the reverse direction is also satisfied: for any statement c, 
   whenever it's executed starting from initial state s and return 
   a new state s' with regard to the relational semantics 'eval_stmt', 
   then there should exist a constant k that statement c starting from 
   s will terminate in state s' within k steps with respect to the 
   functional semantics 'f_eval_stmt';
*)

Ltac apply_rewrite := 
    match goal with
    | h: eval_expr ?s ?e ?s' |- _ => 
        rewrite (f_eval_expr_complete _ _ _ h)
    | h: update _ _ _ = _ |- _ => rewrite h
    | h: updateG _ _ _ = _ |- _ => rewrite h
    | h: f_eval_stmt _ _ _ = _ |- _ => rewrite h
    | h: f_eval_expr _ _ = _ |- _ => rewrite h
    | h: fetch _ _ = _ |- _ => rewrite h
    | h: fetchG _ _ = _ |- _ => rewrite h
    | h: copy_in _ _ _ = _ |- _ => rewrite h
    | h: Copy_in _ _ _ Run_Time_Error |- _ => rewrite <- copy_in_correct2 in h;rewrite h
    | h: Copy_in _ _ _ (Normal _) |- _ => rewrite <- copy_in_correct in h;rewrite h
    | h: cut_until _ _ = Some(_, _) |- _ => rewrite h
    | h: cut_until _ _ = None |- _ => rewrite h
    | h: Cut_until _ _ _ _ |- _ => apply cut_until_correct in h;rewrite h
    end; auto.


Ltac kgreater :=
  repeat
    match goal with
      | h:f_eval_stmt ?k ?s ?p = Normal ?s' |- context [f_eval_stmt (?k + _) ?s ?p] =>
        rewrite (@f_eval_stmt_fixpoint _ _ _ _ h);auto with arith
      | h:f_eval_stmt ?k ?s ?p = Normal ?s' |- context [f_eval_stmt (_ + ?k) ?s ?p] =>
        rewrite (@f_eval_stmt_fixpoint _ _ _ _ h);auto with arith
      | h:f_eval_stmt ?k ?s ?p = Run_Time_Error |- context [f_eval_stmt (?k + _) ?s ?p] =>
        rewrite (@f_eval_stmt_fixpoint_E _ _ _ h);auto with arith
      | h:f_eval_stmt ?k ?s ?p = Run_Time_Error |- context [f_eval_stmt (_ + ?k) ?s ?p] =>
        rewrite (@f_eval_stmt_fixpoint_E _ _ _ h);auto with arith
         end.



Theorem f_eval_stmt_complete : forall s c s',
        eval_stmt s c s' -> (* s' is either a normal state or a run time error *)
            exists k, f_eval_stmt k s c = s'.
Proof. 
  !intros.
  !induction heval_stmt;
  try match goal with
  [ h: eval_expr ?s ?e Run_Time_Error |- exists k, _ = Run_Time_Error] => 
          exists 1%nat; simpl;
          rewrite (f_eval_expr_complete _ _ _ h);
          reflexivity
  end.
  (* 1. S_Assignment *)
  - exists 1%nat; simpl.
    repeat apply_rewrite.
  (* 2. S_Sequence *)
  - destrEx.
    exists (S k); simpl.
    apply_rewrite.
  - destrEx.
    exists (S (k0+k)); simpl.
    kgreater.
    specialize (eval_stmt_state _ _ _ heval_stmt); intros hz1.
    destruct hz1 as [hz2 | hz2]; try rm_exists; subst;
    kgreater.
  (* 3. S_If *)
  - destrEx.
    exists (S k); simpl.
    apply_rewrite.
  - exists 1%nat; simpl.
    apply_rewrite.
  (* 4. S_While_Loop *)
  - destrEx.
    exists (S k); simpl.
    repeat apply_rewrite.
  - destrEx.
    exists (S (k0+k)); simpl.
    apply_rewrite.
    kgreater.
    specialize (eval_stmt_state _ _ _ heval_stmt); intros hz1.
    destruct hz1 as [hz2 | hz2]; try rm_exists; subst;
    kgreater.
  - exists 1%nat; simpl.
    apply_rewrite.
  - exists 1%nat; simpl.
    repeat progress apply_rewrite.
  - exists 1%nat; simpl.
    subst.
    repeat apply_rewrite.
    apply f_eval_decl_complete in heval_decl.
    rewrite heval_decl.
    reflexivity.
  - destruct IHheval_stmt as [k IH].
    exists (S k).
    simpl.
    repeat apply_rewrite.
    apply f_eval_decl_complete in heval_decl.
    rewrite heval_decl.
    apply_rewrite.
  - destruct IHheval_stmt as [k IH].
    exists (S k).
    simpl.
    subst.
    repeat apply_rewrite.
    apply f_eval_decl_complete in heval_decl.
    rewrite heval_decl.
    repeat apply_rewrite.
    repeat setoid_rewrite app_length.
    rewrite heq.
    assert (heq':Datatypes.length slocal + Datatypes.length prefix' -
        Datatypes.length prefix' = Datatypes.length slocal) by omega.
    rewrite heq'.
    rewrite split1_complete with (l2:=prefix') (l1:=slocal).
    + apply copy_out_correct.
      assumption.
    + reflexivity.
    + reflexivity.
Qed.

(**********************************************************************)
(**********************************************************************)

(** * Subprogram Semantics *)

(** In the current SPARK subset, there is no procedure call, 
    so right now we only define the semantics for the main procedure.
    And it can be used to test the tool chain from SPARK source code 
    to Coq evaluation; Later, we will add the procedure call and 
    modify the following procedure semantics;
*)

(** all declared variables in the same procedure should have unique 
    names; 
*)

(** relational (eval_decl) and functional (f_eval_decl) semantics for 
    variable declaration;
*)

(** for any initial state s, after executing the declaration d, 
    it either returns a normal state s' or a run time error;
    (for any variable declaration, if its initialization expression 
     fails the run time checks, for example division by zero or overflow, 
     then it returns an exception)
*)

Lemma eval_decl_state : forall s sto d s',
        eval_decl s sto d s' -> (* s' is either a normal state or a run time error *)
            (exists t, s' = Normal t) \/ s' = Run_Time_Error.
Proof.
    intros s sto d s' h.
    induction h;
    try match goal with
    | [ |- (exists t, Normal ?t1 = Normal t) \/ _ ] => left; exists t1; reflexivity
    | [ |- context [ _ \/ ?A = ?A ] ] => right; reflexivity
    end; auto.
Qed.


(** f_eval_decl completeness and correctness proofs *)

(** bisimulation proof between f_eval_decl and eval_decl: 
    - f_eval_decl_correct
    - f_eval_decl_complete
*)

Lemma f_eval_decl_correct_: forall d s sto s',
    (f_eval_decl s sto d = (Normal s') -> eval_decl s sto d (Normal s')) /\
    (f_eval_decl s sto d = Run_Time_Error -> eval_decl s sto d Run_Time_Error).
Proof.
    intros d s sto.
    intros s'.
    split;intro h.
    - apply f_eval_decl_correct.
      assumption.
    - apply f_eval_decl_correct2.
      assumption.
Qed.


(* = = = = = = Subprogram Body = = = = = =  *)
(** relational and functional semantics for procedure body; *)
(* Is this still needed for global procedures? probably not. *)
(* main procedure has no argument, so we give the nil store as
   parameter store *)
Inductive eval_proc: stack -> procedure_declaration -> Return stack -> Prop :=
    | eval_Proc_E: forall f s,
        eval_decl s nil (procedure_declarative_part f) Run_Time_Error ->
        eval_proc s f Run_Time_Error
    | eval_Proc: forall f s1 s2 s3,
        eval_decl s1 nil (procedure_declarative_part f) (Normal s2) ->
        eval_stmt (s2::s1) (procedure_statements f) s3 ->
        eval_proc s1 f s3.

Function f_eval_proc k (s: stack) (f: procedure_declaration): Return stack :=
    match (f_eval_decl s nil (procedure_declarative_part f)) with
    | Normal s' => f_eval_stmt k (s'::s) (procedure_statements f)
    | Run_Time_Error => Run_Time_Error
    | Abnormal => Abnormal
    | Unterminated => Unterminated
    end.


(** ** Main Procedure Evaluation Without Parameters *)

(** relational and functional semantics for main procedure; *)

Inductive eval_subprogram: stack -> subprogram -> Return stack -> Prop :=
    | eval_Procedure: forall s s' ast_num f,
        eval_proc s f s' ->
        eval_subprogram s (Global_Procedure ast_num f) s'.

Function f_eval_subprogram k (s: stack) (f: subprogram): Return stack := 
    match f with 
    | Global_Procedure ast_num f' => f_eval_proc k s f'
    end.

(** ** Bisimulation Between Relational And Functional Semantics For Main Procedure *)

(** *** f_eval_subprogram_correct *)
Theorem f_eval_subprogram_correct: forall k s f s',
    (f_eval_subprogram k s f = Normal s' -> 
        eval_subprogram s f (Normal s')) /\
    (f_eval_subprogram k s f = Run_Time_Error -> 
        eval_subprogram s f Run_Time_Error).
Proof.
    intros.
    !! (split; intros;
        destruct f;
        simpl in H;
        constructor;
        unfold f_eval_proc in H ;
        remember (f_eval_decl s nil (procedure_declarative_part p)) as x;
        symmetry in Heqx).
  - (* normal state *)
    destruct x; !invclear heq.
    econstructor.
    + apply f_eval_decl_correct.
      apply heqeval_decl.
    + rewrite heqeval_stmt.
      apply f_eval_stmt_correct in heqeval_stmt;assumption.
  - (* run time error *)
    destruct x; !invclear heq; subst.
    + econstructor.
       * apply f_eval_decl_correct in heqeval_decl.
         apply heqeval_decl.
       * rewrite heqeval_stmt.
         apply f_eval_stmt_correct in heqeval_stmt; assumption.
    + econstructor.
      apply f_eval_decl_correct2 in heqeval_decl; assumption.
Qed.

(** *** f_eval_subprogram_complete *)
Theorem f_eval_subprogram_complete: forall s f s',
    eval_subprogram s f s' ->
    exists k, f_eval_subprogram k s f = s'.
Proof.
  intros s f s' h.
  unfold f_eval_subprogram.
  unfold f_eval_proc.
  !invclear h.
  !invclear H;simpl.
  - exists 0.
    apply f_eval_decl_complete in heval_decl.
    rewrite heval_decl.
    reflexivity.
  - apply f_eval_decl_complete in heval_decl.
    rewrite heval_decl.
    apply f_eval_stmt_complete in heval_stmt.
    assumption.
Qed.

(** * Replaying examples using the correctness of functional semantics *)
Module ExampleProcedures2.
(* EXAMPLE 1, v102 is a variable in the scope.
------------------------
procedure P2 () is
  V4 : TYPE5 := 34;
begin
  V102 := 56;
end 
-----------------------
*)
Definition proc1:procedure_declaration := (mkprocedure_declaration
           1 2 nil nil
             (D_Object_declaration
                {|
                  declaration_astnum := 3;
                  object_name := 4;
                  object_nominal_subtype :=  5;
                  initialization_expression := Some (E_Literal 6 (Integer_Literal(34)))
                |}
             )
             (S_Assignment 12 102 (E_Literal 8 (Integer_Literal(56))))).

Definition s1:store := (101,Procedure proc1) :: (102, Value (Int(77))) :: nil.

Definition s2:store := (101,Procedure proc1) :: (102, Value (Int(56)))  :: nil.

Eval vm_compute in f_eval_stmt 200 (s1::nil) (S_ProcCall 13 101 nil).

Lemma essai: eval_stmt (s1::nil) (S_ProcCall 13 101 nil) (Normal (s2::nil)).
Proof.
  apply f_eval_stmt_correct1 with (k:=2).
  compute.f_eval_proc k s f'
    end.

(** ** Bisimulation Between Relational And Functional Semantics For Main Procedure *)

(** *** f_eval_subprogram_correct *)
Theorem f_eval_subprogram_correct: forall k s f s',
    (f_eval_subprogram k s f = Normal s' -> 
        eval_subprogram s f (Normal s')) /\
    (f_eval_subprogram k s f = Run_Time_Error -> 
        eval_subprogram s f Run_Time_Error).
Proof.
    intros.
    !! (split; intros;
        destruct f;
        simpl in H;
        constructor;
        unfold f_eval_proc in H ;
        remember (f_eval_decl s nil (procedure_declarative_part p)) as x;
        symmetry in Heqx).
  - (* normal state *)
    destruct x; !invclear heq.
    econstructor.
    + apply f_eval_decl_correct.
      apply heqeval_decl.
    + rewrite heqeval_stmt.
      apply f_eval_stmt_correct in heqeval_stmt;assumption.
  - (* run time error *)
    destruct x; !invclear heq; subst.
    + econstructor.
       * apply f_eval_decl_correct in heqeval_decl.
         apply heqeval_decl.
       * rewrite heqeval_stmt.
         apply f_eval_stmt_correct in heqeval_stmt; assumption.
    + econstructor.
      apply f_eval_decl_correct2 in heqeval_decl; assumption.
Qed.

(** *** f_eval_subprogram_complete *)
Theorem f_eval_subprogram_complete: forall s f s',
    eval_subprogram s f s' ->
    exists k, f_eval_subprogram k s f = s'.
Proof.
  intros s f s' h.
  unfold f_eval_subprogram.
  unfold f_eval_proc.
  !invclear h.
  !invclear H;simpl.
  - exists 0.
    apply f_eval_decl_complete in heval_decl.
    rewrite heval_decl.
    reflexivity.
  - apply f_eval_decl_complete in heval_decl.
    rewrite heval_decl.
    apply f_eval_stmt_complete in heval_stmt.
    assumption.
Qed.


  reflexivity.
Qed.



(* v102 is a variable in the scope.
procedure P2 () is
  V4 : TYPE5 := 34;
  V5 : TYPE5 := 37;
begin
  V5 := V4 + V5;
  V102 := V5*2;
end 
*)
Definition proc2:procedure_declaration := (mkprocedure_declaration
           1 2 nil nil
             (D_Sequence
                (D_Object_declaration
                   {|
                     declaration_astnum := 3;
                     object_name := 4;
                     object_nominal_subtype :=  5;
                     initialization_expression := Some (E_Literal 6 (Integer_Literal(34)))
                   |}
                )
                (D_Object_declaration
                   {|
                     declaration_astnum := 4;
                     object_name := 5;
                     object_nominal_subtype :=  5;
                     initialization_expression := Some (E_Literal 6 (Integer_Literal(37)))
                   |}
                )
             )
             (S_Sequence 13
                (S_Assignment 14 5
                              (E_Binary_Operation 9 Plus
                                                  (E_Identifier 10 5)
                                                  (E_Identifier 10 4)))
                (S_Assignment
                   12
                   102
                   (E_Binary_Operation 9 Multiply
                                       (E_Identifier 10 5)
                                       (E_Literal 8 (Integer_Literal(2))))))).

Definition s3:store := (101,Procedure proc2) :: (102, Value (Int(77))) :: nil.

Definition s4:store := (101,Procedure proc2) :: (102, Value (Int(142)))  :: nil.


Lemma essai2: eval_stmt (s3::nil) (S_ProcCall 13 101 nil) (Normal (s4::nil)).
Proof.
  apply f_eval_stmt_correct1 with (k:=200).
  vm_compute.
  reflexivity.
Qed.


End ExampleProcedures2.
(* END EXAMPLE *)

**********************************************************************************************************)
