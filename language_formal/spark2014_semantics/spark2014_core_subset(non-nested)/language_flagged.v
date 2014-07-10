Require Export language.
Require Export checks.

(* This file was auto-generated from language_template.v (do not modify) *)

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

Inductive expression_x: Type := 
    | E_Literal_X: astnum -> literal -> check_flags -> expression_x (* 4.2 *)
    | E_Name_X: astnum -> name_x -> check_flags -> expression_x (* 4.1 *)
    | E_Binary_Operation_X: astnum -> binary_operator -> expression_x -> expression_x -> check_flags -> expression_x (* 4.5.3 and 4.5.5 *)
    | E_Unary_Operation_X: astnum -> unary_operator -> expression_x -> check_flags -> expression_x (* 4.5.4 *)  

with name_x: Type := (* 4.1 *)
    | E_Identifier_X: astnum -> idnum -> check_flags -> name_x (* 4.1 *)
    | E_Indexed_Component_X: astnum -> astnum -> idnum -> expression_x -> check_flags -> name_x (* 4.1.1 *)
    | E_Selected_Component_X: astnum -> astnum -> idnum -> idnum -> check_flags -> name_x (* 4.1.3 *). (* the first astnum for the record field and second one for record *)

(** ** Statements *)
(* Chapter 5 *)
(* Sequence is not a statement in Ada, it's a shortcut for now;
   check flags can be easily added if they are needed later;
*)
Inductive statement_x: Type := 
    | S_Null_X: statement_x (* 5.1 *)
    | S_Assignment_X: astnum -> name_x -> expression_x -> statement_x (* 5.2 *)
    | S_If_X: astnum -> expression_x -> statement_x -> statement_x -> statement_x (* 5.3 *)
    | S_While_Loop_X: astnum -> expression_x -> statement_x -> statement_x (* 5.5 *)
    | S_Procedure_Call_X: astnum -> astnum -> procnum -> list expression_x -> statement_x (* 6.4 *) (* the second astnum for the called procedure *)
    | S_Sequence_X: astnum -> statement_x -> statement_x -> statement_x. (* 5.1 *)

(* Array / Record Type Declaration *)
Inductive type_declaration_x: Type := (* 3.2.1 *)
    | Array_Type_Declaration_X: (* Constrained_Array_Definition, non-nested one-dimentional array *)
        astnum -> typenum (*array name*) -> type (*component type*) -> 
          Z (*lower bound*) -> Z (*upper bound*) -> type_declaration_x (* 3.6 *)
    | Record_Type_Declaration_X: 
        astnum -> typenum (*record name*) -> list (idnum * type (*field type*)) -> type_declaration_x (* 3.8 *).

(* 3.3.1 *)
Record object_declaration_x: Type := mkobject_declaration_x{
    declaration_astnum_x: astnum;
    object_name_x: idnum;
    object_nominal_subtype_x: type;
    initialization_expression_x: option (expression_x)
}.

(* 6.1 (15/3) *)
Record parameter_specification_x: Type := mkparameter_specification_x{
    parameter_astnum_x: astnum;
    parameter_name_x: idnum;
    parameter_subtype_mark_x: type;
    parameter_mode_x: mode
(*  parameter_default_expression_x: option (expression_x) *)
}.

(* 13.1.1 *)
Record aspect_specification_x: Type := mkaspect_specification_x{
    aspect_astnum_x: astnum;
    aspect_mark_x: aspectnum;
    aspect_definition_x: expression_x
}.

(* Mutual records/inductives are not allowed in coq, so we build a record by hand. *)
Inductive declaration_x: Type :=  (* 3.1 *)
    | D_Object_Declaration_X: astnum -> object_declaration_x -> declaration_x (* 3.3.1 *) 
    | D_Procedure_Declaration_X: astnum -> procedure_declaration_x -> declaration_x (* 6.1 *)
    | D_Type_Declaration_X: astnum -> type_declaration_x -> declaration_x (* 3.2.1 *)
 (* | package_declaration 
    | Other_Declarations *)

with procedure_declaration_x: Type :=
  mkprocedure_declaration_x
    (procedure_astnum_x: astnum)
    (procedure_name_x: procnum)
    (procedure_parameter_profile_x: list parameter_specification_x)
    (procedure_contracts_x: list aspect_specification_x)
    (procedure_declarative_part_x: list declaration_x)
    (procedure_statements_x: statement_x).


(** ** Compilation Unit Subprogram *)
(* 6.1 *)
Inductive subprogram_x: Type := 
    | Global_Procedure_X: astnum -> procedure_declaration_x -> subprogram_x.
(*  | Global_Function_X: astnum -> function_declaration_x -> subprogram_x *)

(* 10.1.1 *)
Inductive library_unit_declaration_x: Type := 
    | Library_Subprogram_X: astnum -> subprogram_x -> library_unit_declaration_x.

(* 10.1.1 *)
Inductive compilation_unit_x: Type := 
    | Library_Unit_X: astnum -> library_unit_declaration_x -> compilation_unit_x.


(** ** Auxiliary Functions *)

Section AuxiliaryFunctions_X.

  Definition procedure_statements_x pb :=
    match pb with 
      | mkprocedure_declaration_x _ _ _ _ _ x => x
    end.

  Definition procedure_declarative_part_x pb :=
    match pb with
      | mkprocedure_declaration_x _ _ _ _ x _ => x
    end.

  Definition procedure_contracts_x pb :=
    match pb with
      | mkprocedure_declaration_x _ _ _ x _ _ => x
    end.

  Definition procedure_parameter_profile_x pb :=
    match pb with
      | mkprocedure_declaration_x _ _ x _ _ _ => x
    end.

  Definition procedure_name_x pb :=
    match pb with
      | mkprocedure_declaration_x _ x _ _ _ _ => x
    end.

  Definition type_name_x td :=
    match td with
    | Array_Type_Declaration_X _ tn _ _ _ => tn
    | Record_Type_Declaration_X _ tn _ => tn
    end.

End AuxiliaryFunctions_X.











