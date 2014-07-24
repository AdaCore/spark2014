(*_1_Require Export language_basics._1_*)
(*_2_Require Export language._2_*)
(*_2_Require Export checks._2_*)

(* NOTICE *)

(** * SPARK Subset Language *)

(** We use the Ada terminology to define the terms of this subset 
    language, which makes it easy for Ada(SPARK) users to read it;
    Besides, we also indicate the reference chapter (for example, ,3.5.3)
    in Ada 2012 RM, and formalize the language in the same (not exactly) 
    order as they are defined in Ada 2012 RM;
*)

(* Ada 2012 RM, Chapter 3. Declaration and Types *)

(** ** Expressions *)
(* Chapter 4 *)

Inductive expression_xx: Type := 
    | E_Literal_XX: astnum -> literal (*checks*)-> expression_xx (* 4.2 *)
    | E_Name_XX: astnum -> name_xx (*checks*)-> expression_xx (* 4.1 *)
    | E_Binary_Operation_XX: astnum -> binary_operator -> expression_xx -> expression_xx (*checks*)-> expression_xx (* 4.5.3 and 4.5.5 *)
    | E_Unary_Operation_XX: astnum -> unary_operator -> expression_xx (*checks*)-> expression_xx (* 4.5.4 *)  

with name_xx: Type := (* 4.1 *)
    | E_Identifier_XX: astnum -> idnum (*checks*)-> name_xx (* 4.1 *)
    | E_Indexed_Component_XX: astnum -> astnum -> idnum -> expression_xx (*checks*)-> name_xx (* 4.1.1 *)
    | E_Selected_Component_XX: astnum -> astnum -> idnum -> idnum (*checks*)-> name_xx (* 4.1.3 *). (* the first astnum for the record field and second one for record *)

(** ** Statements *)
(* Chapter 5 *)
(* Sequence is not a statement in Ada, it's a shortcut for now;
   check flags can be easily added if they are needed later;
*)
Inductive statement_xx: Type := 
    | S_Null_XX: statement_xx (* 5.1 *)
    | S_Assignment_XX: astnum -> name_xx -> expression_xx -> statement_xx (* 5.2 *)
    | S_If_XX: astnum -> expression_xx -> statement_xx -> statement_xx -> statement_xx (* 5.3 *)
    | S_While_Loop_XX: astnum -> expression_xx -> statement_xx -> statement_xx (* 5.5 *)
    | S_Procedure_Call_XX: astnum -> astnum -> procnum -> list expression_xx -> statement_xx (* 6.4 *) (* the second astnum for the called procedure *)
    | S_Sequence_XX: astnum -> statement_xx -> statement_xx -> statement_xx (* 5.1 *).

Inductive range_xx: Type := Range_XX (l: Z) (u: Z). (* 3.5 *)

(* Array / Record Type Declaration *)
Inductive type_declaration_xx: Type := (* 3.2.1 *)
    | Subtype_Declaration_XX:
        astnum -> typenum (*subtype name*) -> type -> range_xx -> type_declaration_xx (* 3.2.2 *)
    | Derived_Type_Declaration_XX:
        astnum -> typenum (*derived type name*) -> type -> range_xx -> type_declaration_xx (* 3.4 *)
    | Integer_Type_Declaration_XX:
        astnum -> typenum (*integer type name*) -> range_xx -> type_declaration_xx (* 3.5.4 *)
    | Array_Type_Declaration_SubtypeMark_XX: (* Constrained_Array_Definition, non-nested one-dimentional array *)
        astnum -> typenum (*array name*) -> type (*subtype mark*) -> type (*component type*) -> type_declaration_xx (* 3.6 *)
    | Array_Type_Declaration_Range_XX: (* Constrained_Array_Definition, non-nested one-dimentional array *)
        astnum -> typenum (*array name*) -> range_xx -> type (*component type*) -> type_declaration_xx (* 3.6 *)
    | Record_Type_Declaration_XX:
        astnum -> typenum (*record name*) -> list (idnum * type (*field type*)) -> type_declaration_xx (* 3.8 *).

(* 3.3.1 *)
Record object_declaration_xx: Type := mkobject_declaration_xx{
    declaration_astnum_xx: astnum;
    object_name_xx: idnum;
    object_nominal_subtype_xx: type;
    initialization_expression_xx: option (expression_xx)
}.

(* 6.1 (15/3) *)
Record parameter_specification_xx: Type := mkparameter_specification_xx{
    parameter_astnum_xx: astnum;
    parameter_name_xx: idnum;
    parameter_subtype_mark_xx: type;
    parameter_mode_xx: mode
(*  parameter_default_expression_xx: option (expression_xx) *)
}.

(* Mutual records/inductives are not allowed in coq, so we build a record by hand. *)
Inductive declaration_xx: Type :=  (* 3.1 *)
    | D_Null_Declaration_XX: declaration_xx
    | D_Type_Declaration_XX: astnum -> type_declaration_xx -> declaration_xx (* 3.2.1 *)
    | D_Object_Declaration_XX: astnum -> object_declaration_xx -> declaration_xx (* 3.3.1 *) 
    | D_Procedure_Body_XX: astnum -> procedure_body_xx -> declaration_xx (* 6.1 *)
    | D_Seq_Declaration_XX: astnum -> declaration_xx -> declaration_xx -> declaration_xx (* it's introduced for easy proof *)
 (* | package_declaration 
    | Other_Declarations *)

with procedure_body_xx: Type :=
  mkprocedure_body_xx
    (procedure_astnum_xx: astnum)
    (procedure_name_xx: procnum)
    (procedure_parameter_profile_xx: list parameter_specification_xx)
    (procedure_declarative_part_xx: declaration_xx)
    (procedure_statements_xx: statement_xx).


(** ** Auxiliary Functions *)

Section AuxiliaryFunctions_XX.

  Definition procedure_statements_xx pb :=
    match pb with 
      | mkprocedure_body_xx _ _ _ _ x => x
    end.

  Definition procedure_declarative_part_xx pb :=
    match pb with
      | mkprocedure_body_xx _ _ _ x _ => x
    end.

  Definition procedure_parameter_profile_xx pb :=
    match pb with
      | mkprocedure_body_xx _ _ x _ _ => x
    end.

  Definition procedure_name_xx pb :=
    match pb with
      | mkprocedure_body_xx _ x _ _ _ => x
    end.

  Definition type_name_xx td :=
    match td with
    | Subtype_Declaration_XX _ tn _ _                => tn
    | Derived_Type_Declaration_XX _ tn _ _           => tn
    | Integer_Type_Declaration_XX _ tn _             => tn
    | Array_Type_Declaration_SubtypeMark_XX _ tn _ _ => tn
    | Array_Type_Declaration_Range_XX _ tn _ _       => tn
    | Record_Type_Declaration_XX _ tn _              => tn
    end.

  Definition subtype_range_xx (t: type_declaration_xx): option range_xx :=
    match t with
    | Subtype_Declaration_XX ast_num tn t r      => Some r
    | Derived_Type_Declaration_XX ast_num tn t r => Some r
    | Integer_Type_Declaration_XX ast_num tn r   => Some r
    | _                                          => None
    end.

  Definition expression_astnum_xx e :=
    match e with
    | E_Literal_XX ast_num l (*checkflags*)=> ast_num
    | E_Name_XX ast_num n (*checkflags*)=> ast_num
    | E_Binary_Operation_XX ast_num bop e1 e2 (*checkflags*)=> ast_num
    | E_Unary_Operation_XX ast_num uop e (*checkflags*)=> ast_num
    end.  

  Definition name_astnum_xx n :=
    match n with
    | E_Identifier_XX ast_num x (*checkflags*)=> ast_num
    | E_Indexed_Component_XX ast_num x_ast_num x e (*checkflags*)=> ast_num
    | E_Selected_Component_XX ast_num x_ast_num x f (*checkflags*)=> ast_num
    end.

End AuxiliaryFunctions_XX.











