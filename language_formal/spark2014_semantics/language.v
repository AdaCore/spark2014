(* *********************************************************************)
(*                                                                                                *)
(*              Formalization of SPARK 2014 Subset                      *)
(*                                                                                                *)
(*                Zhi Zhang, Kansas State University                        *)
(*                                                                                                *)
(*  Copyright and licence to be determined by KSU.                 *)
(*                                                                                                *)
(* *********************************************************************)

(** 
_AUTHOR_

<<
Zhi Zhang
Departmnt of Computer and Information Sciences
Kansas State University
zhangzhi@ksu.edu
>>
*)

Require Export ZArith.
Require Export Coq.Lists.List.
Require Export Coq.Bool.Bool.
Require Export Coq.Strings.String.

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

Record type_table: Type := mktype_table{
    tt_exptype_table: list (astnum * typenum);
    tt_typename_table: list (typenum * (typeuri * option typedeclnum))
}.

(* ========================================== *)

(** ** Literals *)
Inductive literal: Type :=
	| Integer_Literal: Z -> literal (* 2.4 *)
        | Boolean_Literal: bool -> literal (* 3.5.3 *).

(** unary and binary operators *)
Inductive unary_operator: Type := 
        | Not: unary_operator.
(*     
        | Unary_Plus: unary_operator
	| Unary_Minus: unary_operator. *)

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

(* Ada 2012 RM, Chapter 3. Declaration and Types *)

(** Note: now we only consider the 32-bit singed integer type for 
    our SPARK subset language, and model it with _Integer_; Actually,
    SPARK has various integer types, we can extend our types by 
    adding more SPARK types here and adding its corresponding value
    definition in values.v;
*)
Inductive type: Type := 
    | Boolean: type (* 3.5.3 *)
    | Integer: type (* 3.5.4 *).

(** ** Expressions *)
(* Chapter 4 *)
Inductive expression: Type := 
	| E_Literal: astnum -> literal -> expression (* 4.2 *)
	| E_Identifier: astnum -> idnum -> expression (* 4.1 *)
	| E_Binary_Operation: astnum -> binary_operator -> expression -> expression -> expression (* 4.5.3 and 4.5.5 *)
	| E_Unary_Operation: astnum -> unary_operator -> expression -> expression (* 4.5.4 *).

(** ** Statements *)
(* Chapter 5 *)
(* Sequence is not a statement in Ada, it's a shortcut for now *)
Inductive statement: Type := 
	| S_Assignment: astnum -> idnum -> expression -> statement (* 5.2 *)
	| S_If: astnum -> expression -> statement -> statement (* 5.3 *)
	| S_While_Loop: astnum -> expression -> statement -> statement (* 5.5 *)
	| S_Sequence: astnum -> statement -> statement -> statement (* 5.1 *).

(* 6.2 *)
Inductive mode: Type := 
    | In: mode
    | Out: mode
    | In_Out: mode.

(* 3.3.1 *)
Record object_declaration: Type := mkobject_declaration{
	declaration_astnum: astnum;
        object_name: idnum;
	object_nominal_subtype: typenum;
	initialization_expression: option (expression)
}.

(* 6.1 (15/3) *)
Record parameter_specification: Type := mkparameter_specification{
	parameter_astnum: astnum;
        parameter_name: idnum;
	parameter_subtype_mark: typenum;
	parameter_mode: mode;
	parameter_default_expression: option (expression)
}.

(* 13.1.1 *)
Record aspect_specification: Type := mkaspect_specification{
	aspect_astnum: astnum;
	aspect_mark: aspectnum;
	aspect_definition: expression
}.

(* 6.3 *)
Record procedure_body: Type := mkprocedure_body{
	procedure_astnum: astnum;
	procedure_name: procnum;
	procedure_contracts: list aspect_specification;
	procedure_parameter_profile: list parameter_specification;
	procedure_declarative_part: list object_declaration;
	procedure_statements: statement
}.

(* 6.3 *)
Record function_body: Type := mkfunction_body{
	function_astnum: astnum;
	function_name: procnum;
	function_result_subtype: type; (* 6.5 (3/2) *)
	function_contracts: list aspect_specification;
	function_parameter_profile: list parameter_specification;
	function_declarative_part: list object_declaration;
	function_statements: statement
}.

(** ** Compilation unit: subprogram *)
(* 6.1 *)
Inductive subprogram: Type := 
	| Procedure: astnum -> procedure_body -> subprogram
(*	| Function: astnum -> function_body -> subprogram *).

(* 10.1.1 *)
Inductive library_unit_declaration: Type := 
	| Library_Subprogram: astnum -> subprogram -> library_unit_declaration.

(* 10.1.1 *)
Inductive compilation_unit: Type := 
	| Library_Unit: astnum -> library_unit_declaration -> type_table -> compilation_unit.
