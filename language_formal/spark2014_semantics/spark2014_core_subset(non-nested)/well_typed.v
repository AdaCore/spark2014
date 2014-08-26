Require Export semantics_flagged.
Require Export checks_optimization.



(** * Well-Typed Stack *)
Section Well_Typed_Stack_Sec.
(** the value of variable and and record field are well-typed according to
    the symbol table;

  extract_array_index_range_x st arraytyp (Range_X l u) ->
  do_range_check i l u Success ->
  STACK.fetchG x s = Some (AggregateV (ArrayV a)) ->
  array_select a i = Some (Int v) ->
  valueO_of_array_component_type st arraytyp (IntBetween l' u') ->
  (Zge_bool v l') && (Zle_bool v u') = true.



  fetch_exp_type_x recAstNum st = Some (Record_Type t) ->
  valueO_of_record_field_type st recType fieldId (IntBetween l u) ->
  STACK.fetchG x s = Some (AggregateV (RecordV r)) ->
  record_select r fieldId = Some (Int v) ->
   (v >=? l)%Z && (v <=? u)%Z = true

    TODO: to be completed !
 *)
Inductive well_typed_stack: symboltable_x -> STACK.stack -> Prop :=
  | WTS: forall st s,
      well_typed_stack st s. 

(** for any variable in stack, its value should be in the domain of its type 
    
    TODO: to be proved !
*)
Axiom variable_value_in_type_domain: forall st s x_ast_num x v t l u,
  well_typed_stack st s ->
    eval_name_x st s (E_Identifier_X x_ast_num x nil) (Normal (BasicV (Int v))) ->
      fetch_exp_type_x x_ast_num st = Some t ->
        valueO_of_type st t (IntBetween l u) ->
          (Zge_bool v l) && (Zle_bool v u) = true.

End Well_Typed_Stack_Sec.
