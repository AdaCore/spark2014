(* *********************************************************************)
(*                                                                     *)
(*              Formalization of SPARK 2014 Subset                     *)
(*                                                                     *)
(* *********************************************************************)

Require Export ZArith.
Require Export Coq.Lists.List.
Require Export Coq.Bool.Bool.
Require Export Coq.Strings.String.
Require Export more_list.

(* 1. command to generate HTML document from Coq source files: 
       coqdoc language.v values.v environment.v util.v checks.v semantics.v wellformedness.v propertyProof.v -toc --no-lib-name
    2. compile all the Coq files 
       coqc language.v values.v environment.v util.v checks.v semantics.v wellformedness.v propertyProof.v
*)

(** * SPARK Subset Language *)

(** We use the Ada terminology to define the terms of this subset 
    language, which makes it easy for Ada(SPARK) users to read it;
    Besides, we also indicate the reference chapter (for example, ,3.5.3)
    in Ada 2012 RM, and formalize the language in the same (not exactly) 
    order as they are defined in Ada 2012 RM;
*)

(* ========================================== *)

(** Distinct AST number labeled for each AST node; it's not the part  
    of the SPARK language subset, it's introduced only for internal 
    use, for example, it can be used to locate the source of the errors,
    to collect type information for expression node, and to map ast node
    to its run time check flags and so on;
*)

Definition astnum := nat.

(** In CompCert, Cminor uses non-negative values to represent 
    identifiers, we follow this style by using natural numbers 
    to represent dentifiers/names;
*)

Definition idnum := nat.

Definition procnum := nat.

Definition typenum := nat.

Definition typedeclnum := astnum.

Definition aspectnum := nat.

Definition typeuri := string.

Definition index := Z. (* array index *)

Record type_table: Type := mktype_table{
    tt_exptype_table: list (astnum * typenum);
    tt_typename_table: list (typenum * (typeuri * option typedeclnum))
}.

(* ========================================== *)
(** Note: now we only consider the 32-bit singed integer type for 
    our SPARK subset language, and model it with _Integer_; Actually,
    SPARK has various integer types, we can extend our types by 
    adding more SPARK types here and adding its corresponding value
    definition in values.v;
*)

Inductive type: Type :=
    | Boolean (* 3.5.3 *)
    | Integer (* 3.5.4 *)
    | Aggregate (t: typenum) (* 3.6, 3.8 *) (* t: declared array/record type name *).

(** unary and binary operators *)
Inductive unary_operator: Type := 
    | Not: unary_operator     
    | Unary_Plus: unary_operator
    | Unary_Minus: unary_operator.

Inductive binary_operator: Type := 
    | Equal: binary_operator 
    | Not_Equal: binary_operator
    | Greater_Than: binary_operator
    | Greater_Than_Or_Equal: binary_operator
    | Less_Than: binary_operator
    | Less_Than_Or_Equal: binary_operator
    | And: binary_operator
    | Or: binary_operator
    | Plus: binary_operator
    | Minus: binary_operator
    | Multiply: binary_operator
    | Divide: binary_operator.

(** ** Literals *)
Inductive literal: Type :=
    | Integer_Literal: Z -> literal (* 2.4 *)
    | Boolean_Literal: bool -> literal (* 3.5.3 *).

(* Ada 2012 RM, Chapter 3. Declaration and Types *)

(** ** Expressions *)
(* Chapter 4 *)
Inductive expression: Type := 
    | E_Literal: astnum -> literal -> expression (* 4.2 *)
    | E_Name: astnum -> name -> expression (* 4.1 *)
    | E_Binary_Operation: astnum -> binary_operator -> expression -> expression -> expression (* 4.5.3 and 4.5.5 *)
    | E_Unary_Operation: astnum -> unary_operator -> expression -> expression (* 4.5.4 *)  
(*  | E_Named_Array_Aggregate: astnum -> list (index * expression) -> expression (* 4.3.3 *)
    | E_Named_Record_Aggregate: astnum -> list ((astnum * idnum) * expression) -> expression (* 4.3.1 *)
*)

with name: Type := (* 4.1 *)
    | E_Identifier: astnum -> idnum -> name (* 4.1 *)
    | E_Indexed_Component: astnum -> astnum -> idnum -> expression -> name (* 4.1.1 *)
    | E_Selected_Component: astnum -> astnum -> idnum -> idnum -> name (* 4.1.3 *). (* the first astnum for the record field and second one for record *)

(** ** Statements *)
(* Chapter 5 *)
(* Sequence is not a statement in Ada, it's a shortcut for now *)
Inductive statement: Type := 
    | S_Null: statement (* 5.1 *)
    | S_Assignment: astnum -> name -> expression -> statement (* 5.2 *)
    | S_If: astnum -> expression -> statement -> statement -> statement (* 5.3 *)
    | S_While_Loop: astnum -> expression -> statement -> statement (* 5.5 *)
    | S_Procedure_Call: astnum -> astnum -> procnum -> list expression -> statement (* 6.4 *) (* the second astnum for the called procedure *)
    | S_Sequence: astnum -> statement -> statement -> statement (* 5.1 *).

(* 6.2 *)
Inductive mode: Type := 
    | In
    | Out
    | In_Out.

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
    (procedure_contracts: list aspect_specification)
    (procedure_parameter_profile: list parameter_specification)
    (procedure_declarative_part: list declaration)
    (procedure_statements: statement).


(** ** Compilation unit: subprogram *)
(* 6.1 *)
Inductive subprogram: Type := 
    | Global_Procedure: astnum -> procedure_declaration -> subprogram
(*  | Global_Function: astnum -> function_declaration -> subprogram *).

(* 10.1.1 *)
Inductive library_unit_declaration: Type := 
    | Library_Subprogram: astnum -> subprogram -> library_unit_declaration.

(* 10.1.1 *)
Inductive compilation_unit: Type := 
    | Library_Unit: astnum -> library_unit_declaration -> type_table -> compilation_unit.


Section AuxiliaryFunctions.
  (* We define projection functions by hand too. *)
  Definition procedure_statements pb :=
    match pb with 
      | mkprocedure_declaration _ _ _ _ _ x => x
    end.

  Definition procedure_declarative_part pb :=
    match pb with
      | mkprocedure_declaration _ _ _ _ x _ => x
    end.

  Definition procedure_parameter_profile pb :=
    match pb with
      | mkprocedure_declaration _ _ _ x _ _ => x
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

  (** Some useful definition, related to language structures *)

  (** [Is_var e] means that expression [e] is a variable *)
  Definition Is_var e:Prop :=
    match e with
      |  E_Identifier _ _ => True
      | _ => False
    end.

  (** functional version of Is_var above *)
  Definition is_var e:bool :=
    match e with
      |  E_Identifier _ _ => true
      | _ => false
    end.

  (** correctness of is_var. *)
  Lemma is_var_Is_var : forall e, is_var e = true <-> Is_var e.
  Proof.
    intros e.
    destruct e;simpl; split;intro h;auto;try contradiction; discriminate h. 
  Qed.

  (* this is an equivalent of inversion  *)
  Ltac inversion_is_var H :=
    match (type of H) with
      | is_var ?e = true =>
        rewrite is_var_Is_var in H; destruct e;simpl in H; try contradiction;subst
      | is_var ?e = false =>
        rewrite is_var_Is_var in H; destruct e;simpl in H; try contradiction;subst
    end.

  (* this is an equivalent of inversion  *)
  Ltac inversion_is_var_auto :=
    try match goal with
          | H: is_var ?e = true |- _ =>
            rewrite is_var_Is_var in H
            ; destruct e;simpl in H; try contradiction;subst
          | H: is_var ?e = false |- _ =>
            rewrite is_var_Is_var in H
            ; destruct e;simpl in H; try contradiction;subst
        end.

End AuxiliaryFunctions.


