Require Export environment.
Require Export checks.
Require Export language_flagged.
Require Export semantics_flagged.


(** * value types for run time checks optimization *)
(** value is represented by a range, for a variable, if its initial value is undefined 
    or it's a parameter or its value is dynamically determined, then we use the range 
    of its type as its value, e.g. x: Integer; it's value is: (IntBetween Integer'First Integer'Last),
    x: Integer := 1; it's value is: (IntBetween 1 1);
    for boolean value, it doesn't matter whether it's true or false, so we just use BoolValue to 
    represent boolean value;
 *)
Inductive valueO : Type :=
  | IntBetween (l : Z) (u: Z)
  | BoolValue.

Inductive valueO_of_type: symboltable_x -> type -> valueO -> Prop :=
  | ValueO_Of_Integer: forall st,
      valueO_of_type st Integer (IntBetween min_signed max_signed)
  | ValueO_Of_Subtype: forall st t l u,
      extract_subtype_range_x st t (Range_X l u) ->
      valueO_of_type st t (IntBetween l u).

(** t: type id of the array type; (l, u) is the domain of the array component type *)
Inductive valueO_of_array_component_type : symboltable_x -> typenum -> valueO -> Prop :=
  | Array_Component_Value : forall t st ast_num tn indexSubtypeMark componentType l u,
      fetch_type_x t st = Some (Array_Type_Declaration_X ast_num tn indexSubtypeMark componentType) ->
      valueO_of_type st componentType (IntBetween l u) ->
      valueO_of_array_component_type st t (IntBetween l u).

Function record_field_type (r: list (idnum * type)) (f: idnum): option type :=
    match r with 
    | (f1, t1) :: r1 =>
        if beq_nat f1 f then 
          Some t1
        else
          record_field_type r1 f
    | nil => None 
    end.

(** t: type id of the record type; f: field id; ft: field type id *)
Inductive valueO_of_record_field_type : symboltable_x -> typenum -> idnum -> valueO -> Prop :=
  | Record_Field_Value : forall t st ast_num tn fields f ft l u,
      fetch_type_x t st = Some (Record_Type_Declaration_X ast_num tn fields) ->
      record_field_type fields f = Some ft ->
      valueO_of_type st ft (IntBetween l u) ->
      valueO_of_record_field_type st t f (IntBetween l u).


Definition eval_literalO (l: literal): valueO :=
  match l with
  | Integer_Literal v => IntBetween v v
  | Boolean_Literal v => BoolValue
  end.

(** remove those checks whose run time checking are always successful *)
Inductive optimize_checks_on_binop: check_flags -> binary_operator -> value -> value -> check_flags -> Prop :=
    | O_No_Check_Binop: forall op v1 v2,
        optimize_checks_on_binop nil op v1 v2 nil
    | O_Checks_Pass_Binop: forall ck op v1 v2 cks cks',
        ck = Do_Overflow_Check \/ ck = Do_Division_Check ->
        do_flagged_check_on_binop ck op v1 v2 Success ->
        optimize_checks_on_binop cks op v1 v2 cks' ->
        optimize_checks_on_binop (ck :: cks) op v1 v2 cks'
    | O_Checks_Fail_Binop: forall ck op v1 v2 msg cks cks',
        ck = Do_Overflow_Check \/ ck = Do_Division_Check ->
        do_flagged_check_on_binop ck op v1 v2 (Exception msg) ->
        optimize_checks_on_binop cks op v1 v2 cks' ->
        optimize_checks_on_binop (ck :: cks) op v1 v2 (ck :: cks')
    | O_Checks_Other_Binop: forall op cks v1 v2 cks' ck,
        ck <> Do_Overflow_Check /\ ck <> Do_Division_Check ->
        optimize_checks_on_binop cks op v1 v2 cks' ->
        optimize_checks_on_binop (ck :: cks) op v1 v2 (ck :: cks').

Inductive optimize_checks_on_unop: check_flags -> unary_operator -> value -> check_flags -> Prop :=
    | O_No_Check_Unop: forall op v,
        optimize_checks_on_unop nil op v nil
    | O_Checks_Pass_Unop: forall ck op v cks cks',
        ck = Do_Overflow_Check ->
        do_flagged_check_on_unop ck op v Success ->
        optimize_checks_on_unop cks op v cks' ->
        optimize_checks_on_unop (ck :: cks) op v cks'
    | O_Checks_Fail_Unop: forall ck op v msg cks cks',
        ck = Do_Overflow_Check ->
        do_flagged_check_on_unop ck op v (Exception msg) ->
        optimize_checks_on_unop cks op v cks' ->
        optimize_checks_on_unop (ck :: cks) op v (ck :: cks')
    | O_Checks_Other_Unop: forall ck cks op v cks',
        ck <> Do_Overflow_Check ->
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
Inductive eval_adding_lower_upper: binary_operator -> (Z * Z) -> (Z * Z) -> (Z * Z) -> Prop :=
  | LU_Plus: forall l1 u1 l2 u2,
      eval_adding_lower_upper Plus (l1, u1) (l2, u2) ((l1 + l2)%Z, (u1 + u2)%Z)
  | LU_Minus: forall l1 u1 l2 u2,
      eval_adding_lower_upper Minus (l1, u1) (l2, u2) ((l1 - u2)%Z, (u1 - l2)%Z).

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
  

(** * Run-Time Checks Optimization For Expression *)
(** given an expression, optimize its run time checks, and return 
    its possible range values, which will be used later to optimize
    other checks;
  - do_division_check
  - do_overflow_check
  - do_range_check
*)

Inductive optimize_expression_x: symboltable_x -> expression_x -> (valueO * expression_x) -> Prop :=
  | O_Literal_X: forall l v st ast_num checkflags,
      eval_literalO l = v ->
      optimize_expression_x st (E_Literal_X ast_num l checkflags) (v, (E_Literal_X ast_num l checkflags))
  | O_Name_X: forall st n v n' ast_num,
      optimize_name_x st n (v, n') ->
      optimize_expression_x st (E_Name_X ast_num n nil) (v, (E_Name_X ast_num n' nil))
  | O_Binary_Plus_Operation_X: forall st e1 l1 u1 e1' e2 l2 u2 e2' checkflags cks1 cks2 checkflags' ast_num,
      optimize_expression_x st e1 ((IntBetween l1 u1), e1') ->
      optimize_expression_x st e2 ((IntBetween l2 u2), e2') ->
      optimize_checks_on_binop checkflags Plus (BasicV (Int l1)) (BasicV (Int l2)) cks1 ->
      optimize_checks_on_binop checkflags Plus (BasicV (Int u1)) (BasicV (Int u2)) cks2 ->
      checkflags' = union cks1 cks2 ->
      ~(List.In Do_Overflow_Check checkflags') ->
      optimize_expression_x st (E_Binary_Operation_X ast_num Plus e1 e2 checkflags) 
                               (IntBetween (l1 + l2)%Z (u1 + u2)%Z, (E_Binary_Operation_X ast_num Plus e1' e2' checkflags'))
  | O_Binary_Plus_Operation_Overflow_X: forall st e1 l1 u1 e1' e2 l2 u2 e2' checkflags cks1 cks2 checkflags' ast_num,
      optimize_expression_x st e1 ((IntBetween l1 u1), e1') ->
      optimize_expression_x st e2 ((IntBetween l2 u2), e2') ->
      optimize_checks_on_binop checkflags Plus (BasicV (Int l1)) (BasicV (Int l2)) cks1 ->
      optimize_checks_on_binop checkflags Plus (BasicV (Int u1)) (BasicV (Int u2)) cks2 ->
      checkflags' = union cks1 cks2 ->
      List.In Do_Overflow_Check checkflags' ->
      optimize_expression_x st (E_Binary_Operation_X ast_num Plus e1 e2 checkflags) 
                               (IntBetween min_signed max_signed, (E_Binary_Operation_X ast_num Plus e1' e2' checkflags'))
  | O_Binary_Minus_Operation_X: forall st e1 l1 u1 e1' e2 l2 u2 e2' checkflags cks1 cks2 checkflags' ast_num,
      optimize_expression_x st e1 ((IntBetween l1 u1), e1') ->
      optimize_expression_x st e2 ((IntBetween l2 u2), e2') ->
      optimize_checks_on_binop checkflags Minus (BasicV (Int l1)) (BasicV (Int l2)) cks1 ->
      optimize_checks_on_binop checkflags Minus (BasicV (Int u1)) (BasicV (Int u2)) cks2 ->
      checkflags' = union cks1 cks2 ->
      ~(List.In Do_Overflow_Check checkflags') ->
      optimize_expression_x st (E_Binary_Operation_X ast_num Minus e1 e2 checkflags) 
                               (IntBetween (l1 - u2)%Z (u1 - l2)%Z, (E_Binary_Operation_X ast_num Minus e1' e2' checkflags'))
  | O_Binary_Minus_Operation_Overflow_X: forall st e1 l1 u1 e1' e2 l2 u2 e2' checkflags cks1 cks2 checkflags' ast_num,
      optimize_expression_x st e1 ((IntBetween l1 u1), e1') ->
      optimize_expression_x st e2 ((IntBetween l2 u2), e2') ->
      optimize_checks_on_binop checkflags Minus (BasicV (Int l1)) (BasicV (Int l2)) cks1 ->
      optimize_checks_on_binop checkflags Minus (BasicV (Int u1)) (BasicV (Int u2)) cks2 ->
      checkflags' = union cks1 cks2 ->
      ~(List.In Do_Overflow_Check checkflags') ->
      optimize_expression_x st (E_Binary_Operation_X ast_num Minus e1 e2 checkflags) 
                               (IntBetween min_signed max_signed, (E_Binary_Operation_X ast_num Minus e1' e2' checkflags'))
  | O_Binary_Multiplying_Operation_X: forall op st e1 l1 u1 e1' e2 l2 u2 e2' ast_num t l u checkflags,
      op = Multiply \/ op = Divide ->
      optimize_expression_x st e1 ((IntBetween l1 u1), e1') ->
      optimize_expression_x st e2 ((IntBetween l2 u2), e2') ->
      fetch_exp_type_x ast_num st = Some t ->
      valueO_of_type st t (IntBetween l u) ->
      optimize_expression_x st (E_Binary_Operation_X ast_num op e1 e2 checkflags) 
                               (IntBetween l u, (E_Binary_Operation_X ast_num op e1' e2' checkflags))
  | O_Binary_Logical_Operation_X: forall op st e1 e1' e2 e2' ast_num checkflags,
      op <> Plus /\ op <> Minus /\ op <> Multiply /\ op <> Divide ->
      optimize_expression_x st e1 (BoolValue, e1') ->
      optimize_expression_x st e2 (BoolValue, e2') ->
      optimize_expression_x st (E_Binary_Operation_X ast_num op e1 e2 checkflags) 
                               (BoolValue, (E_Binary_Operation_X ast_num op e1' e2' checkflags))

(*
  | O_Binary_Multiply_Operation_X: forall st e1 l1 u1 e1' e2 l2 u2 e2' checkflags cks1 cks2 checkflags' ast_num,
      optimize_expression_x st e1 ((IntBetween l1 u1), e1') ->
      optimize_expression_x st e2 ((IntBetween l2 u2), e2') ->
      optimize_checks_on_binop checkflags Multiply (BasicV (Int l1)) (BasicV (Int l2)) cks1 ->
      optimize_checks_on_binop checkflags Multiply (BasicV (Int u1)) (BasicV (Int u2)) cks2 ->
      checkflags' = union cks1 cks2 ->
      optimize_expression_x st (E_Binary_Operation_X ast_num Multiply e1 e2 checkflags) 
                               (IntBetween (l1 - u2)%Z (u1 - l2)%Z, (E_Binary_Operation_X ast_num Multiply e1' e2' checkflags'))
  | O_Binary_Divide_Operation_X: forall st e1 l1 u1 e1' e2 l2 u2 e2' checkflags cks1 cks2 checkflags' ast_num,
      optimize_expression_x st e1 ((IntBetween l1 u1), e1') ->
      optimize_expression_x st e2 ((IntBetween l2 u2), e2') ->
      optimize_checks_on_binop checkflags Divide (BasicV (Int l1)) (BasicV (Int l2)) cks1 ->
      optimize_checks_on_binop checkflags Divide (BasicV (Int u1)) (BasicV (Int u2)) cks2 ->
      checkflags' = union cks1 cks2 ->
      optimize_expression_x st (E_Binary_Operation_X ast_num Divide e1 e2 checkflags) 
                               (IntBetween (l1 - u2)%Z (u1 - l2)%Z, (E_Binary_Operation_X ast_num Divide e1' e2' checkflags'))
*)
  | O_Unary_Minus_Operation_X: forall st e l u e' l' u' checkflags cks1 cks2 checkflags' ast_num,
      optimize_expression_x st e (IntBetween l u, e') ->
      Z.opp u = l' ->
      Z.opp l = u' ->
      optimize_checks_on_unop checkflags Unary_Minus (BasicV (Int l')) cks1 ->
      optimize_checks_on_unop checkflags Unary_Minus (BasicV (Int u')) cks2 -> 
      checkflags' = union cks1 cks2 ->
      ~(List.In Do_Overflow_Check checkflags') ->
      optimize_expression_x st (E_Unary_Operation_X ast_num Unary_Minus e checkflags) 
                               (IntBetween l' u', (E_Unary_Operation_X ast_num Unary_Minus e' checkflags'))
  | O_Unary_Minus_Operation_Overflow_X: forall st e l u e' l' u' checkflags cks1 cks2 checkflags' ast_num,
      optimize_expression_x st e (IntBetween l u, e') ->
      Z.opp u = l' ->
      Z.opp l = u' ->
      optimize_checks_on_unop checkflags Unary_Minus (BasicV (Int l')) cks1 ->
      optimize_checks_on_unop checkflags Unary_Minus (BasicV (Int u')) cks2 -> 
      checkflags' = union cks1 cks2 ->
      List.In Do_Overflow_Check checkflags' ->
      optimize_expression_x st (E_Unary_Operation_X ast_num Unary_Minus e checkflags) 
                               (IntBetween min_signed max_signed, (E_Unary_Operation_X ast_num Unary_Minus e' checkflags'))
  | O_Unary_Plus_Operation_X: forall st e l u e' ast_num checkflags,
      optimize_expression_x st e (IntBetween l u, e') ->
      optimize_expression_x st (E_Unary_Operation_X ast_num Unary_Plus e checkflags) 
                               (IntBetween l u, (E_Unary_Operation_X ast_num Unary_Plus e' checkflags))
  | O_Unary_Not_Operation_X: forall st e e' ast_num checkflags,
      optimize_expression_x st e (BoolValue, e') ->
      optimize_expression_x st (E_Unary_Operation_X ast_num Not e checkflags)
                               (BoolValue, (E_Unary_Operation_X ast_num Not e' checkflags))
      
with optimize_name_x: symboltable_x -> name_x -> (valueO * name_x) -> Prop :=
  | O_Identifier_X: forall ast_num st t l u x checkflags,
      fetch_exp_type_x ast_num st = Some t ->
      valueO_of_type st t (IntBetween l u) ->
      optimize_name_x st (E_Identifier_X ast_num x checkflags) (IntBetween l u, (E_Identifier_X ast_num x checkflags))
  | O_Indexed_Component_X: forall e st l u e' x_ast_num t l' u' ast_num x checkflags,
      ~(List.In Do_Range_Check (exp_check_flags e)) ->
      optimize_expression_x st e (IntBetween l u, e') ->
      fetch_exp_type_x x_ast_num st = Some (Array_Type t) ->
      valueO_of_array_component_type st t (IntBetween l' u') ->
      optimize_name_x st (E_Indexed_Component_X ast_num x_ast_num x e checkflags) 
                         (IntBetween l' u', (E_Indexed_Component_X ast_num x_ast_num x e' checkflags))
  | O_Indexed_Component_Range_Pass_X: forall e cks1 cks2 st l u e' x_ast_num t l' u' l'' u'' ast_num x checkflags,
      exp_check_flags e = cks1 ++ Do_Range_Check :: cks2 ->
      optimize_expression_x st (update_exp_check_flags e (cks1 ++ cks2)) (IntBetween l u, e') ->
      fetch_exp_type_x x_ast_num st = Some (Array_Type t) ->
      extract_array_index_range_x st t (Range_X l' u') -> (* range value of array index type *)
      valueO_of_array_component_type st t (IntBetween l'' u'') ->
      do_range_check l l' u' Success ->
      do_range_check u l' u' Success ->
      optimize_name_x st (E_Indexed_Component_X ast_num x_ast_num x e checkflags) 
                         (IntBetween l'' u'', (E_Indexed_Component_X ast_num x_ast_num x e' checkflags))
  | O_Indexed_Component_Range_Fail_X: forall e cks1 cks2 st l u e' x_ast_num t l' u' l'' u'' ast_num x checkflags,
      exp_check_flags e = cks1 ++ Do_Range_Check :: cks2 ->
      optimize_expression_x st e (IntBetween l u, e') ->
      fetch_exp_type_x x_ast_num st = Some (Array_Type t) ->
      extract_array_index_range_x st t (Range_X l' u') -> (* range value of array index type *)
      valueO_of_array_component_type st t (IntBetween l'' u'') ->
      do_range_check l l' u' (Exception RTE_Range) \/ do_range_check u l' u' (Exception RTE_Range) ->
      optimize_name_x st (E_Indexed_Component_X ast_num x_ast_num x e checkflags) 
                         (IntBetween l'' u'', (E_Indexed_Component_X ast_num x_ast_num x e' checkflags))
  | O_Selected_Component_X: forall x_ast_num st t f l u ast_num x checkflags,
      fetch_exp_type_x x_ast_num st = Some (Record_Type t) ->
      valueO_of_record_field_type st t f (IntBetween l u) ->
      optimize_name_x st (E_Selected_Component_X ast_num x_ast_num x f checkflags)
                         (IntBetween l u, (E_Selected_Component_X ast_num x_ast_num x f checkflags)).


(** optimize run-time checks for arguments during procedure call;
    for a procedure call, given a list of arguments and its corresponding formal parameters,
    optimize its run-time checks (that's range check);
*)

Inductive optimize_args_x: symboltable_x -> list parameter_specification_x -> list expression_x -> list expression_x -> Prop :=
  | O_Args_Nil: forall st,
      optimize_args_x st nil nil nil
  | O_Args_Head_In: forall param arg st v arg' params args args',
      param.(parameter_mode_x) = In -> 
      ~(List.In Do_Range_Check (exp_check_flags arg)) ->
      optimize_expression_x st arg (v, arg') ->
      optimize_args_x st params args args' ->
      optimize_args_x st (param :: params) (arg :: args) (arg' :: args')
  | O_Args_Head_In_Range_Pass: forall param arg cks1 cks2 st l u arg' l' u' params args args',
      param.(parameter_mode_x) = In -> 
      exp_check_flags arg = cks1 ++ Do_Range_Check :: cks2 ->
      optimize_expression_x st (update_exp_check_flags arg (cks1 ++ cks2)) (IntBetween l u, arg') ->
      extract_subtype_range_x st (param.(parameter_subtype_mark_x)) (Range_X l' u') ->
      do_range_check l l' u' Success ->
      do_range_check u l' u' Success ->
      optimize_args_x st params args args' ->
      optimize_args_x st (param :: params) (arg :: args) (arg' :: args')
  | O_Args_Head_In_Range_Fail: forall param arg cks1 cks2 st l u arg' l' u' params args args',
      param.(parameter_mode_x) = In -> 
      exp_check_flags arg = cks1 ++ Do_Range_Check :: cks2 ->
      optimize_expression_x st arg (IntBetween l u, arg') ->
      extract_subtype_range_x st (param.(parameter_subtype_mark_x)) (Range_X l' u') ->
      do_range_check l l' u' (Exception RTE_Range) \/ do_range_check u l' u' (Exception RTE_Range) ->
      optimize_args_x st params args args' ->
      optimize_args_x st (param :: params) (arg :: args) (arg' :: args')
  | O_Args_Head_Out: forall param checkflags st params args args' ast_num x_ast_num x,
      param.(parameter_mode_x) = Out -> 
      ~(List.In Do_Range_Check_On_CopyOut checkflags) ->
      optimize_args_x st params args args' ->
      optimize_args_x st (param :: params) ((E_Name_X ast_num (E_Identifier_X x_ast_num x checkflags) nil) :: args) 
                                           ((E_Name_X ast_num (E_Identifier_X x_ast_num x checkflags) nil) :: args')
  | O_Args_Head_Out_Range_Pass: forall param checkflags cks1 cks2 st l u ast_num t l' u' params args args' x_ast_num x,
      param.(parameter_mode_x) = Out -> 
      checkflags = cks1 ++ Do_Range_Check_On_CopyOut :: cks2 ->
      extract_subtype_range_x st (param.(parameter_subtype_mark_x)) (Range_X l u) ->
      fetch_exp_type_x ast_num st = Some t ->
      extract_subtype_range_x st t (Range_X l' u') ->
      do_range_check l l' u' Success ->
      do_range_check u l' u' Success ->
      optimize_args_x st params args args' ->
      optimize_args_x st (param :: params) ((E_Name_X ast_num (E_Identifier_X x_ast_num x checkflags) nil) :: args) 
                                           ((E_Name_X ast_num (E_Identifier_X x_ast_num x (cks1 ++ cks2)) nil) :: args')
  | O_Args_Head_Out_Range_Fail: forall param checkflags cks1 cks2 st l u ast_num t l' u' params args args' x_ast_num x,
      param.(parameter_mode_x) = Out -> 
      checkflags = cks1 ++ Do_Range_Check_On_CopyOut :: cks2 ->
      extract_subtype_range_x st (param.(parameter_subtype_mark_x)) (Range_X l u) ->
      fetch_exp_type_x ast_num st = Some t ->
      extract_subtype_range_x st t (Range_X l' u') ->
      do_range_check l l' u' (Exception RTE_Range) \/ do_range_check u l' u' (Exception RTE_Range) ->
      optimize_args_x st params args args' ->
      optimize_args_x st (param :: params) ((E_Name_X ast_num (E_Identifier_X x_ast_num x checkflags) nil) :: args) 
                                           ((E_Name_X ast_num (E_Identifier_X x_ast_num x checkflags) nil) :: args')
  | O_Args_Head_InOut: forall param checkflags st params args args' ast_num x_ast_num x,
      param.(parameter_mode_x) = In_Out -> 
      ~(List.In Do_Range_Check_On_CopyOut checkflags) ->
      ~(List.In Do_Range_Check checkflags) ->
      optimize_args_x st params args args' ->
      optimize_args_x st (param :: params) ((E_Name_X ast_num (E_Identifier_X x_ast_num x checkflags) nil) :: args) 
                                           ((E_Name_X ast_num (E_Identifier_X x_ast_num x checkflags) nil) :: args')
  | O_Args_Head_InOut_In_Range_Pass: forall param checkflags cks1 cks2 ast_num st t l u l' u' params args args' x_ast_num x,
      param.(parameter_mode_x) = In_Out -> 
      ~(List.In Do_Range_Check_On_CopyOut checkflags) ->
      checkflags = cks1 ++ Do_Range_Check :: cks2 ->
      fetch_exp_type_x ast_num st = Some t ->
      extract_subtype_range_x st t (Range_X l u) ->
      extract_subtype_range_x st (param.(parameter_subtype_mark_x)) (Range_X l' u') ->
      do_range_check l l' u' Success ->
      do_range_check u l' u' Success ->
      optimize_args_x st params args args' ->
      optimize_args_x st (param :: params) ((E_Name_X ast_num (E_Identifier_X x_ast_num x checkflags) nil) :: args) 
                                           ((E_Name_X ast_num (E_Identifier_X x_ast_num x (cks1 ++ cks2)) nil) :: args')
  | O_Args_Head_InOut_In_Range_Fail: forall param checkflags cks1 cks2 ast_num st t l u l' u' params args args' x_ast_num x,
      param.(parameter_mode_x) = In_Out -> 
      ~(List.In Do_Range_Check_On_CopyOut checkflags) ->
      checkflags = cks1 ++ Do_Range_Check :: cks2 ->
      fetch_exp_type_x ast_num st = Some t ->
      extract_subtype_range_x st t (Range_X l u) ->
      extract_subtype_range_x st (param.(parameter_subtype_mark_x)) (Range_X l' u') ->
      do_range_check l l' u' (Exception RTE_Range) \/ do_range_check u l' u' (Exception RTE_Range) ->
      optimize_args_x st params args args' ->
      optimize_args_x st (param :: params) ((E_Name_X ast_num (E_Identifier_X x_ast_num x checkflags) nil) :: args) 
                                           ((E_Name_X ast_num (E_Identifier_X x_ast_num x checkflags) nil) :: args')
  | O_Args_Head_InOut_Out_Range_Pass: forall param checkflags cks1 cks2 st l u ast_num t l' u' params args args' x_ast_num x,
      param.(parameter_mode_x) = In_Out -> 
      ~(List.In Do_Range_Check checkflags) ->
      checkflags = cks1 ++ Do_Range_Check_On_CopyOut :: cks2 ->
      extract_subtype_range_x st (param.(parameter_subtype_mark_x)) (Range_X l u) ->
      fetch_exp_type_x ast_num st = Some t ->
      extract_subtype_range_x st t (Range_X l' u') ->
      do_range_check l l' u' Success ->
      do_range_check u l' u' Success ->
      optimize_args_x st params args args' ->
      optimize_args_x st (param :: params) ((E_Name_X ast_num (E_Identifier_X x_ast_num x checkflags) nil) :: args) 
                                           ((E_Name_X ast_num (E_Identifier_X x_ast_num x (cks1 ++ cks2)) nil) :: args')
  | O_Args_Head_InOut_Out_Range_Fail: forall param checkflags cks1 cks2 st l u ast_num t l' u' params args args' x_ast_num x,
      param.(parameter_mode_x) = In_Out -> 
      ~(List.In Do_Range_Check checkflags) ->
      checkflags = cks1 ++ Do_Range_Check_On_CopyOut :: cks2 ->
      extract_subtype_range_x st (param.(parameter_subtype_mark_x)) (Range_X l u) ->
      fetch_exp_type_x ast_num st = Some t ->
      extract_subtype_range_x st t (Range_X l' u') ->
      do_range_check l l' u' (Exception RTE_Range) \/ do_range_check u l' u' (Exception RTE_Range) ->
      optimize_args_x st params args args' ->
      optimize_args_x st (param :: params) ((E_Name_X ast_num (E_Identifier_X x_ast_num x checkflags) nil) :: args) 
                                           ((E_Name_X ast_num (E_Identifier_X x_ast_num x checkflags) nil) :: args')
  | O_Args_Head_InOut_InOut_Range_Pass: forall param checkflags cks1 cks2 cks1' cks2' st l u ast_num t l' u' 
                                               params args args' x_ast_num x,
      param.(parameter_mode_x) = In_Out ->
      checkflags = cks1 ++ Do_Range_Check :: cks2 ->
      cks1 ++ cks2 = cks1' ++ Do_Range_Check_On_CopyOut :: cks2' ->
      extract_subtype_range_x st (param.(parameter_subtype_mark_x)) (Range_X l u) ->
      fetch_exp_type_x ast_num st = Some t ->
      extract_subtype_range_x st t (Range_X l' u') ->
      do_range_check l l' u' Success /\ do_range_check u l' u' Success -> (* it's the same as: l=l' /\ u=u' *)
      do_range_check l' l u Success /\ do_range_check u' l u Success ->
      optimize_args_x st params args args' ->
      optimize_args_x st (param :: params) ((E_Name_X ast_num (E_Identifier_X x_ast_num x checkflags) nil) :: args) 
                                           ((E_Name_X ast_num (E_Identifier_X x_ast_num x (cks1' ++ cks2')) nil) :: args')
  | O_Args_Head_InOut_InOut_In_Range_Pass: forall param checkflags cks1 cks2 cks1' cks2' st l u ast_num t l' u' 
                                               params args args' x_ast_num x,
      param.(parameter_mode_x) = In_Out ->
      checkflags = cks1 ++ Do_Range_Check :: cks2 ->
      cks1 ++ cks2 = cks1' ++ Do_Range_Check_On_CopyOut :: cks2' ->
      extract_subtype_range_x st (param.(parameter_subtype_mark_x)) (Range_X l u) ->
      fetch_exp_type_x ast_num st = Some t ->
      extract_subtype_range_x st t (Range_X l' u') ->
      do_range_check l' l u Success /\ do_range_check u' l u Success ->
      do_range_check l l' u' (Exception RTE_Range) \/ do_range_check u l' u' (Exception RTE_Range) ->
      optimize_args_x st params args args' ->
      optimize_args_x st (param :: params) ((E_Name_X ast_num (E_Identifier_X x_ast_num x checkflags) nil) :: args) 
                                           ((E_Name_X ast_num (E_Identifier_X x_ast_num x (cks1 ++ cks2)) nil) :: args')
  | O_Args_Head_InOut_InOut_Out_Range_Pass: forall param checkflags cks1 cks2 cks1' cks2' st l u ast_num t l' u' 
                                               params args args' x_ast_num x,
      param.(parameter_mode_x) = In_Out ->
      checkflags = cks1 ++ Do_Range_Check_On_CopyOut :: cks2 ->
      cks1 ++ cks2 = cks1' ++ Do_Range_Check :: cks2' ->
      extract_subtype_range_x st (param.(parameter_subtype_mark_x)) (Range_X l u) ->
      fetch_exp_type_x ast_num st = Some t ->
      extract_subtype_range_x st t (Range_X l' u') ->
      do_range_check l l' u' Success /\ do_range_check u l' u' Success ->
      do_range_check l' l u (Exception RTE_Range) \/ do_range_check u' l u (Exception RTE_Range) ->
      optimize_args_x st params args args' ->
      optimize_args_x st (param :: params) ((E_Name_X ast_num (E_Identifier_X x_ast_num x checkflags) nil) :: args) 
                                           ((E_Name_X ast_num (E_Identifier_X x_ast_num x (cks1 ++ cks2)) nil) :: args')
  | O_Args_Head_InOut_InOut_Out_Range_Fail: forall param checkflags cks1 cks2 cks1' cks2' st l u ast_num t l' u' 
                                               params args args' x_ast_num x,
      param.(parameter_mode_x) = In_Out ->
      checkflags = cks1 ++ Do_Range_Check :: cks2 ->
      cks1 ++ cks2 = cks1' ++ Do_Range_Check_On_CopyOut :: cks2' ->
      extract_subtype_range_x st (param.(parameter_subtype_mark_x)) (Range_X l u) ->
      fetch_exp_type_x ast_num st = Some t ->
      extract_subtype_range_x st t (Range_X l' u') ->
      do_range_check l l' u' (Exception RTE_Range) \/ do_range_check u l' u' (Exception RTE_Range) ->
      do_range_check l' l u (Exception RTE_Range) \/ do_range_check u' l u (Exception RTE_Range) ->
      optimize_args_x st params args args' ->
      optimize_args_x st (param :: params) ((E_Name_X ast_num (E_Identifier_X x_ast_num x checkflags) nil) :: args) 
                                           ((E_Name_X ast_num (E_Identifier_X x_ast_num x checkflags) nil) :: args').


(** * Run-Time Checks Optimization For Statement *)
(** given a statement, optimize its run-time check flags and return a new optimized statement *)
Inductive optimize_statement_x: symboltable_x -> statement_x -> statement_x -> Prop :=
  | O_Null_X: forall st, 
      optimize_statement_x st S_Null_X S_Null_X
  | O_Assignment_X: forall e st v e' x v' x' ast_num,
      ~(List.In Do_Range_Check (exp_check_flags e)) ->
      optimize_expression_x st e (v, e') ->
      optimize_name_x st x (v', x') -> 
      optimize_statement_x st (S_Assignment_X ast_num x e) (S_Assignment_X ast_num x' e')
  | O_Assignment_Range_Pass_X: forall e cks1 cks2 st l u e' x l' u' x' ast_num,
      exp_check_flags e = cks1 ++ Do_Range_Check :: cks2 ->
      optimize_expression_x st (update_exp_check_flags e (cks1 ++ cks2)) (IntBetween l u, e') ->
      optimize_name_x st x (IntBetween l' u', x') ->
      do_range_check l l' u' Success ->
      do_range_check u l' u' Success ->
      optimize_statement_x st (S_Assignment_X ast_num x e) (S_Assignment_X ast_num x' e')
  | O_Assignment_Range_Fail_X: forall e cks1 cks2 st l u e' x l' u' x' ast_num,
      exp_check_flags e = cks1 ++ Do_Range_Check :: cks2 ->
      optimize_expression_x st e (IntBetween l u, e') ->
      optimize_name_x st x (IntBetween l' u', x') ->
      do_range_check l l' u' (Exception RTE_Range) \/ do_range_check u l' u' (Exception RTE_Range) ->
      optimize_statement_x st (S_Assignment_X ast_num x e) (S_Assignment_X ast_num x' e')
  | O_If_X: forall st e v e' c1 c1' c2 c2' ast_num,
      optimize_expression_x st e (v, e') ->
      optimize_statement_x st c1 c1' ->
      optimize_statement_x st c2 c2' ->
      optimize_statement_x st (S_If_X ast_num e c1 c2) (S_If_X ast_num e' c1' c2')
  | O_While_Loop_X: forall st e v e' c c' ast_num,
      optimize_expression_x st e (v, e') ->
      optimize_statement_x st c c' ->
      optimize_statement_x st (S_While_Loop_X ast_num e c) (S_While_Loop_X ast_num e' c')
  | O_Procedure_Call_X: forall p st n pb args args' ast_num p_ast_num,
      fetch_proc_x p st = Some (n, pb) ->
      optimize_args_x st (procedure_parameter_profile_x pb) args args' ->
      optimize_statement_x st (S_Procedure_Call_X ast_num p_ast_num p args) (S_Procedure_Call_X ast_num p_ast_num p args')
  | O_Sequence_X: forall st c1 c1' c2 c2' ast_num,
      optimize_statement_x st c1 c1' ->
      optimize_statement_x st c2 c2' ->
      optimize_statement_x st (S_Sequence_X ast_num c1 c2) (S_Sequence_X ast_num c1' c2').

(** * Run-Time Checks Optimization For Declaration *)
Inductive optimize_declaration_x: symboltable_x -> declaration_x -> declaration_x -> Prop :=
  | O_Null_Declaration_X: forall st,
      optimize_declaration_x st D_Null_Declaration_X D_Null_Declaration_X
  | O_Type_Declaration_X: forall st ast_num t,
      optimize_declaration_x st (D_Type_Declaration_X ast_num t) (D_Type_Declaration_X ast_num t)
  | O_Object_Declaration_No_Initialization_X: forall o st ast_num,
      o.(initialization_expression_x) = None ->
      optimize_declaration_x st (D_Object_Declaration_X ast_num o) (D_Object_Declaration_X ast_num o)
  | O_Object_Declaration_X: forall o e st v e' o' ast_num,
      o.(initialization_expression_x) = Some e ->
      ~(List.In Do_Range_Check (exp_check_flags e)) ->
      optimize_expression_x st e (v, e') -> 
      o' = (mkobject_declaration_x o.(declaration_astnum_x) o.(object_name_x) o.(object_nominal_subtype_x) (Some e')) ->
      optimize_declaration_x st (D_Object_Declaration_X ast_num o) 
                                (D_Object_Declaration_X ast_num o')
  | O_Object_Declaration_Range_Pass_X: forall o e cks1 cks2 st l u e' l' u' o' ast_num,
      o.(initialization_expression_x) = Some e ->
      exp_check_flags e = cks1 ++ Do_Range_Check :: cks2 ->
      optimize_expression_x st (update_exp_check_flags e (cks1 ++ cks2)) (IntBetween l u, e') -> 
      extract_subtype_range_x st (o.(object_nominal_subtype_x)) (Range_X l' u') ->
      do_range_check l l' u' Success ->
      do_range_check u l' u' Success ->      
      o' = (mkobject_declaration_x o.(declaration_astnum_x) o.(object_name_x) o.(object_nominal_subtype_x) (Some e')) ->
      optimize_declaration_x st (D_Object_Declaration_X ast_num o) 
                                (D_Object_Declaration_X ast_num o')
  | O_Object_Declaration_Range_Fail_X: forall o e cks1 cks2 st l u e' l' u' o' ast_num,
      o.(initialization_expression_x) = Some e ->
      exp_check_flags e = cks1 ++ Do_Range_Check :: cks2 ->
      optimize_expression_x st e (IntBetween l u, e') -> 
      extract_subtype_range_x st (o.(object_nominal_subtype_x)) (Range_X l' u') ->
      do_range_check l l' u' (Exception RTE_Range) \/ do_range_check u l' u' (Exception RTE_Range) ->      
      o' = (mkobject_declaration_x o.(declaration_astnum_x) o.(object_name_x) o.(object_nominal_subtype_x) (Some e')) ->
      optimize_declaration_x st (D_Object_Declaration_X ast_num o) 
                                (D_Object_Declaration_X ast_num o')
  | O_Procedure_Body_X: forall st p p' ast_num,
      optimize_procedure_body_x st p p' ->
      optimize_declaration_x st (D_Procedure_Body_X ast_num p) (D_Procedure_Body_X ast_num p')
  | O_Seq_Declaration_X: forall st d1 d1' d2 d2' ast_num,
      optimize_declaration_x st d1 d1' ->
      optimize_declaration_x st d2 d2' ->
      optimize_declaration_x st (D_Seq_Declaration_X ast_num d1 d2) (D_Seq_Declaration_X ast_num d1' d2')

with optimize_procedure_body_x: symboltable_x -> procedure_body_x -> procedure_body_x -> Prop :=
  | O_Procedure_Body: forall st decls decls' stmt stmt' ast_num p params,
      optimize_declaration_x st decls decls' ->
      optimize_statement_x st stmt stmt' ->
      optimize_procedure_body_x st (mkprocedure_body_x ast_num p params decls stmt)
                                   (mkprocedure_body_x ast_num p params decls' stmt').













