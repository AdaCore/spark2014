Require Export environment.
Require Export checks.
Require Export language_flagged.
Require Export semantics_flagged.


(** * value types for run time checks optimization *)
(** value is represented by a range, for a variable, if its initial value is undefined 
    or it's a parameter or its value is dynamically determined, then we use the range 
    of its type as its value, e.g. x: Integer; it's value is: (IntO Integer'First Integer'Last),
    x: Integer := 1; it's value is: (IntO 1 1);
 *)
Inductive basic_valueO : Type :=
    | IntO (l : Z) (u: Z)
    | BoolO (b : bool).

Inductive aggregate_valueO : Type :=
    | ArrayVO (a: list (index * basic_valueO))
    | RecordVO (r: list (idnum * basic_valueO)).

Inductive valueO : Type :=
    | BasicVO (v: basic_valueO)
    | AggregateVO (v: aggregate_valueO)
    | UndefinedO.


Module Entry_Value_Stored <: ENTRY.
  Definition T := valueO.
End Entry_Value_Stored.

Module STACK := STORE(Entry_Value_Stored).
Import STACK.


Inductive extract_type_range_x: symboltable_x -> type -> range_x -> Prop :=
  | Extract_Integer_Range_X: forall st,
      extract_type_range_x st Integer (Range_X min_signed max_signed)
  | Extract_Subtype_Range_X: forall st t l u,
      extract_subtype_range_x st t (Range_X l u) ->
      extract_type_range_x st t (Range_X l u).

Function record_selectO (r: list (idnum * basic_valueO)) (f: idnum): option basic_valueO :=
    match r with 
    | (f1, v1) :: r1 =>
        if beq_nat f1 f then 
          Some v1
        else
          record_selectO r1 f
    | nil => None 
    end.

Function array_selectO (a: list (index * basic_valueO)) (i: Z): option basic_valueO :=
    match a with 
    | (i0, v0) :: a1 =>
        if Zeq_bool i0 i then
          Some v0
        else
          array_selectO a1 i
    | nil => None
    end.

Definition eval_literalO (l: literal): valueO :=
    match l with
    | Integer_Literal v => BasicVO (IntO v v)
    | Boolean_Literal v => BasicVO (BoolO v)
    end.

(** remove those checks whose run time checking are always successful *)
Inductive optimize_checks_on_binop: check_flags -> binary_operator -> value -> value -> check_flags -> Prop :=
    | O_No_Check_Binop: forall op v1 v2,
        optimize_checks_on_binop nil op v1 v2 nil
    | O_Checks_Pass_Binop: forall ck op v1 v2 cks cks',
        do_flagged_check_on_binop ck op v1 v2 Success ->
        optimize_checks_on_binop cks op v1 v2 cks' ->
        optimize_checks_on_binop (ck :: cks) op v1 v2 cks'
    | O_Checks_Fail_Binop: forall ck op v1 v2 msg cks cks',
        do_flagged_check_on_binop ck op v1 v2 (Exception msg) ->
        optimize_checks_on_binop cks op v1 v2 cks' ->
        optimize_checks_on_binop (ck :: cks) op v1 v2 (ck :: cks').

Inductive optimize_checks_on_unop: check_flags -> unary_operator -> value -> check_flags -> Prop :=
    | O_No_Check_Unop: forall op v,
        optimize_checks_on_unop nil op v nil
    | O_Checks_Pass_Unop: forall ck op v cks cks',
        do_flagged_check_on_unop ck op v Success ->
        optimize_checks_on_unop cks op v cks' ->
        optimize_checks_on_unop (ck :: cks) op v cks'
    | O_Checks_Fail_Unop: forall ck op v msg cks cks',
        do_flagged_check_on_unop ck op v (Exception msg) ->
        optimize_checks_on_unop cks op v cks' ->
        optimize_checks_on_unop (ck :: cks) op v (ck :: cks').

(** compute the union of two check flag sets *)
Function union (cks1 cks2: check_flags): check_flags := 
  match cks1 with
  | nil => cks2 
  | ck :: cks1' =>
      if element_of ck cks2 then
        union cks1' cks2 
      else
        ck :: (union cks1' cks2)
  end. 

(** for a value in range (l1, u1) and another value in range (l2, u2),
    compute the value range for their binary operation result;
*)
Inductive eval_lower_upper: binary_operator -> (Z * Z) -> (Z * Z) -> (Z * Z) -> Prop :=
  | LU_Plus: forall l1 u1 l2 u2,
      eval_lower_upper Plus (l1, u1) (l2, u2) ((l1 + l2)%Z, (u1 + u2)%Z)
  | LU_Minus: forall l1 u1 l2 u2,
      eval_lower_upper Minus (l1, u1) (l2, u2) ((l1 - u2)%Z, (u1 - l2)%Z).

(*
Lemma in_range: forall op v1 v2 l1 u1 l2 u2 v3 x1 x2 x3 x4,
  op = Plus \/ op = Minus \/ op = Multiply ->
  v1 >= l1 /\ v1 <= u1 ->
  v2 >= l2 /\ v2 <= u2 ->
  Val.binary_operation op (BasicV (Int v1)) (BasicV (Int v2)) = Some (BasicV (Int v3)) ->
  Val.binary_operation op (BasicV (Int l1)) (BasicV (Int l2)) = Some (BasicV (Int x1)) ->
  Val.binary_operation op (BasicV (Int l1)) (BasicV (Int u2)) = Some (BasicV (Int x2)) ->  
  Val.binary_operation op (BasicV (Int u1)) (BasicV (Int l2)) = Some (BasicV (Int x3)) ->
  Val.binary_operation op (BasicV (Int u1)) (BasicV (Int u2)) = Some (BasicV (Int x4)) ->
  .
*)
  

(** * Optimize Checks for Expression *)
(** given an expression, optimize its run time checks, and return 
    its possible range values, which will be used later to optimize
    other checks;
*)

Inductive optimize_expression_x: symboltable_x -> stack -> expression_x -> (valueO * expression_x) -> Prop :=
  | O_Literal_X: forall l v st s ast_num,
      eval_literalO l = v ->
      optimize_expression_x st s (E_Literal_X ast_num l nil) (v, (E_Literal_X ast_num l nil))
  | O_Name_X: forall st s n v n' ast_num,
      optimize_name_x st s n (v, n') ->
      optimize_expression_x st s (E_Name_X ast_num n nil) (v, (E_Name_X ast_num n' nil))
  | O_Binary_Operation_X: forall st s e1 l1 u1 e1' e2 l2 u2 e2' v1 v2 ast_num op,
      op = Plus \/ op = Minus ->
      optimize_expression_x st s e1 (BasicVO (IntO l1 u1), e1') ->
      optimize_expression_x st s e2 (BasicVO (IntO l2 u2), e2') ->
      eval_lower_upper op (l1, u1) (l2 u2) (v1, v2) ->
      optimize_checks_on_binop checkflags op (BasicV (Int l1)) (BasicV (Int l2)) cks1 ->
      optimize_checks_on_binop checkflags op (BasicV (Int u1)) (BasicV (Int u2)) cks2 ->
      checkflags' = union cks1 cks2 ->
      optimize_expression_x st s (E_Binary_Operation_X ast_num op e1 e2 checkflags) 
                                 (BasicVO (IntO v1 v2), (E_Binary_Operation_X ast_num op e1' e2' checkflags'))

  | O_Binary_Operation_X: forall op st s e1 l1 u1 e1' e2 l2 u2 e2' v1 v2 checkflags cks1 cks2 ast_num,
      op = Plus \/ op = Minus \/ op = Multiply ->
      optimize_expression_x st s e1 (BasicVO (IntO l1 u1), e1') ->
      optimize_expression_x st s e2 (BasicVO (IntO l2 u2), e2') ->
      Val.binary_operation op (BasicV (Int l1)) (BasicV (Int l2)) = Some (BasicV (Int v1)) ->
      Val.binary_operation op (BasicV (Int u1)) (BasicV (Int u2)) = Some (BasicV (Int v2)) ->
      (Zge_bool v1 min_signed) && (Zle_bool v1 max_signed) = true ->
      (Zge_bool v2 min_signed) && (Zle_bool v2 max_signed) = true ->
      checkflags = cks1 ++ Do_Overflow_Check :: cks2 ->
      optimize_expression_x st s (E_Binary_Operation_X ast_num op e1 e2 checkflags) 
                                 (BasicVO (IntO v1 v2), (E_Binary_Operation_X ast_num op e1' e2' (cks1 ++ cks2)))
  | O_Unary_Operation_X: forall op st s e l u e' l' u' checkflags cks1 cks2 ast_num,
      op = Unary_Minus ->
      optimize_expression_x st s e (BasicVO (IntO l u), e') ->
      Z.opp u = l' ->
      Z.opp l = u' ->
      (Zge_bool l' min_signed) && (Zle_bool l' max_signed) = true ->
      (Zge_bool u' min_signed) && (Zle_bool u' max_signed) = true ->
      checkflags = cks1 ++ Do_Overflow_Check :: cks2 ->
      optimize_expression_x st s (E_Unary_Operation_X ast_num op e checkflags) 
                                 (BasicVO (IntO l' u'), (E_Unary_Operation_X ast_num op e' (cks1 ++ cks2)))
      
with optimize_name_x: symboltable_x -> stack -> name_x -> (valueO * name_x) -> Prop :=
  | O_Identifier_X: forall x s v st ast_num,
      fetchG x s = Some v ->
      optimize_name_x st s (E_Identifier_X ast_num x nil) (v, (E_Identifier_X ast_num x nil))
  | O_Indexed_Component_X: forall e cks1 cks2 st s l u e' x x_ast_num t a_ast_num tn tm typ l' u' l'' u'' ast_num,
      exp_check_flags e = cks1 ++ Do_Range_Check :: cks2 ->
      optimize_expression_x st s (update_exp_check_flags e (cks1 ++ cks2)) (BasicVO (IntO l u), e') ->
      fetch_exp_type_x x_ast_num st = Some (Array_Type t) ->
      fetch_type_x t st = Some (Array_Type_Declaration_X a_ast_num tn tm typ) ->
      extract_subtype_range_x st tm (Range_X l' u') -> (* range value of array index type *)
      extract_type_range_x st typ (Range_X l'' u'') -> (* range value of array component type *)
      do_range_check l l' u' Success ->
      do_range_check u l' u' Success ->
      optimize_name_x st s (E_Indexed_Component_X ast_num x_ast_num x e nil) 
                           (BasicVO (IntO l'' u''), (E_Indexed_Component_X ast_num x_ast_num x e' nil))
  | O_Selected_Component_X: forall x s r f v st ast_num x_ast_num,
      fetchG x s = Some (AggregateVO (RecordVO r)) ->
      record_selectO r f = Some v ->
      optimize_name_x st s (E_Selected_Component_X ast_num x_ast_num x f nil)
                           ((BasicVO v), (E_Selected_Component_X ast_num x_ast_num x f nil)).



