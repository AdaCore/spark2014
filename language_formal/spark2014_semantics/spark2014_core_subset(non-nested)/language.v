Require Export language_basics.

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

Inductive expression: Type := 
    | E_Literal: astnum -> literal -> expression (* 4.2 *)
    | E_Name: astnum -> name -> expression (* 4.1 *)
    | E_Binary_Operation: astnum -> binary_operator -> expression -> expression -> expression (* 4.5.3 and 4.5.5 *)
    | E_Unary_Operation: astnum -> unary_operator -> expression -> expression (* 4.5.4 *)  

with name: Type := (* 4.1 *)
    | E_Identifier: astnum -> idnum -> name (* 4.1 *)
    | E_Indexed_Component: astnum -> astnum -> idnum -> expression -> name (* 4.1.1 *)
    | E_Selected_Component: astnum -> astnum -> idnum -> idnum -> name (* 4.1.3 *). (* the first astnum for the record field and second one for record *)

(** ** Statements *)
(* Chapter 5 *)
(* Sequence is not a statement in Ada, it's a shortcut for now;
   check flags can be easily added if they are needed later;
*)
Inductive statement: Type := 
    | S_Null: statement (* 5.1 *)
    | S_Assignment: astnum -> name -> expression -> statement (* 5.2 *)
    | S_If: astnum -> expression -> statement -> statement -> statement (* 5.3 *)
    | S_While_Loop: astnum -> expression -> statement -> statement (* 5.5 *)
    | S_Procedure_Call: astnum -> astnum -> procnum -> list expression -> statement (* 6.4 *) (* the second astnum for the called procedure *)
    | S_Sequence: astnum -> statement -> statement -> statement. (* 5.1 *)

(* Array / Record Type Declaration *)
Inductive type_declaration: Type := (* 3.2.1 *)
    | Array_Type_Declaration: (* Constrained_Array_Definition, non-nested one-dimentional array *)
        astnum -> typenum (*array name*) -> type (*component type*) -> 
          Z (*lower bound*) -> Z (*upper bound*) -> type_declaration (* 3.6 *)
    | Record_Type_Declaration: 
        astnum -> typenum (*record name*) -> list (idnum * type (*field type*)) -> type_declaration (* 3.8 *).

(* 3.3.1 *)
Record object_declaration: Type := mkobject_declaration{
    declaration_astnum: astnum;
    object_name: idnum;
    object_nominal_subtype: type;
    initialization_expression: option (expression)
}.

(* 6.1 (15/3) *)
Record parameter_specification: Type := mkparameter_specification{
    parameter_astnum: astnum;
    parameter_name: idnum;
    parameter_subtype_mark: type;
    parameter_mode: mode
(*  parameter_default_expression: option (expression) *)
}.

(* 13.1.1 *)
Record aspect_specification: Type := mkaspect_specification{
    aspect_astnum: astnum;
    aspect_mark: aspectnum;
    aspect_definition: expression
}.

(* Mutual records/inductives are not allowed in coq, so we build a record by hand. *)
Inductive declaration: Type :=  (* 3.1 *)
    | D_Object_Declaration: astnum -> object_declaration -> declaration (* 3.3.1 *) 
    | D_Procedure_Declaration: astnum -> procedure_declaration -> declaration (* 6.1 *)
    | D_Type_Declaration: astnum -> type_declaration -> declaration (* 3.2.1 *)
 (* | package_declaration 
    | Other_Declarations *)

with procedure_declaration: Type :=
  mkprocedure_declaration
    (procedure_astnum: astnum)
    (procedure_name: procnum)
    (procedure_parameter_profile: list parameter_specification)
    (procedure_contracts: list aspect_specification)
    (procedure_declarative_part: list declaration)
    (procedure_statements: statement).


(** ** Compilation Unit Subprogram *)
(* 6.1 *)
Inductive subprogram: Type := 
    | Global_Procedure: astnum -> procedure_declaration -> subprogram.
(*  | Global_Function: astnum -> function_declaration -> subprogram *)

(* 10.1.1 *)
Inductive library_unit_declaration: Type := 
    | Library_Subprogram: astnum -> subprogram -> library_unit_declaration.

(* 10.1.1 *)
Inductive compilation_unit: Type := 
    | Library_Unit: astnum -> library_unit_declaration -> compilation_unit.


(** ** Auxiliary Functions *)

Section AuxiliaryFunctions.

  Definition procedure_statements pb :=
    match pb with 
      | mkprocedure_declaration _ _ _ _ _ x => x
    end.

  Definition procedure_declarative_part pb :=
    match pb with
      | mkprocedure_declaration _ _ _ _ x _ => x
    end.

  Definition procedure_contracts pb :=
    match pb with
      | mkprocedure_declaration _ _ _ x _ _ => x
    end.

  Definition procedure_parameter_profile pb :=
    match pb with
      | mkprocedure_declaration _ _ x _ _ _ => x
    end.

  Definition procedure_name pb :=
    match pb with
      | mkprocedure_declaration _ x _ _ _ _ => x
    end.

  Definition type_name td :=
    match td with
    | Array_Type_Declaration _ tn _ _ _ => tn
    | Record_Type_Declaration _ tn _ => tn
    end.

End AuxiliaryFunctions.











