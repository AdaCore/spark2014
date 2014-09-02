Require Export ZArith.
Require Export Coq.Lists.List.
Require Export Coq.Bool.Bool.
Require Export CpdtTactics.
Require Export LibTactics.
Require Export more_list.

(** This file defines some basic data types and operations used for
    formalization of SPARK 2014 language;
*)

(** * Identifiers *)

(** Distinct AST number labeled for each AST node; it's not a part  
    of the SPARK 2014 language, but it's introduced to facilitate the 
    formalization of the language and error debugging. For example, the
    AST number can be used to map the error information back to the SPARK 
    source code, and it also can be used to map each ast node to its type 
    information;
*)

Definition astnum := nat.

(** In CompCert, non-negative values are used to represent identifiers, 
    we take the same way to represent identifiers/names as natural numbers;
   - idnum:   represent declared variables;
   - procnum: represent declared procedure names;
   - typenum: represent declared type names;
*)

Definition idnum := nat.

Definition procnum := nat.

Definition typenum := nat.

Definition index := Z. (* array index *)

(*
Record type_table: Type := mktype_table{
    tt_exptype_table: list (astnum * typenum);
    tt_typename_table: list (typenum * (typeuri * option typedeclnum))
}.
*)

(** * Data Types *)
(** in SPARK, data types can be boolean, integer, subtype, array/record 
    types and others; typenum denotes the subtype names or array/record 
    types names;

    In SPARK, subtype can be declared in the following ways:
    - subtype declaration,      e.g. subtype MyInt is Integer range 0 .. 5;
    - derived type declaration, e.g. type MyInt is new Integer range 1 .. 100;
    - integer type declaration, e.g. type MyInt is range 1 .. 10;

    Note: now we only consider the 32-bit singed integer type for 
    our SPARK subset language, and model it with Integer; Actually,
    SPARK has various integer types, we can extend our types by 
    adding more SPARK types here and adding its corresponding value
    definition in values.v;
*)

Inductive type: Type :=
    | Boolean (* 3.5.3 *)
    | Integer (* 3.5.4 *)
    | Subtype (t: typenum) (* 3.2.2 *)     (* t: declared subtype name *)
    | Derived_Type (t: typenum) (* 3.4 *)
    | Integer_Type (t: typenum) (* 3.5.4 *)
    | Array_Type (t: typenum) (* 3.6 *)    (* t: declared array type name *)
    | Record_Type (t: typenum) (* 3.8 *)   (* t: declared record type name *).

(** * In/Out Mode *)

(* 6.2 *)
Inductive mode: Type := 
    | In
    | Out
    | In_Out.

(** * Operators *)

(** unary and binary operators *)
Inductive unary_operator: Type :=      
    | Unary_Plus: unary_operator
    | Unary_Minus: unary_operator
    | Not: unary_operator.

Inductive binary_operator: Type := 
    | And: binary_operator
    | Or: binary_operator
    | Equal: binary_operator 
    | Not_Equal: binary_operator
    | Less_Than: binary_operator
    | Less_Than_Or_Equal: binary_operator
    | Greater_Than: binary_operator
    | Greater_Than_Or_Equal: binary_operator
    | Plus: binary_operator
    | Minus: binary_operator
    | Multiply: binary_operator
    | Divide: binary_operator.

(** * Literals *)

Inductive literal: Type :=
    | Integer_Literal: Z -> literal (* 2.4 *)
    | Boolean_Literal: bool -> literal (* 3.5.3 *).

(** * Auxiliary Functions *)

Section LB_AuxiliaryFunctions.
  
  (** it wll be used to determine whether to put range check *)
  Definition is_range_constrainted_type (t: type): bool :=
    match t with
    | Subtype _      => true
    | Derived_Type _ => true
    | Integer_Type _ => true
    | _              => false
    end.

  Definition subtype_num (t: type): option typenum :=
    match t with
    | Subtype tn      => Some tn
    | Derived_Type tn => Some tn
    | Integer_Type tn => Some tn
    | _               => None
    end.

  Definition beq_type (t1 t2: type): bool :=
    match t1, t2 with
    | Boolean, Boolean => true
    | Integer, Integer => true
    | Subtype t1', Subtype t2' => beq_nat t1' t2'
    | Derived_Type t1', Derived_Type t2' => beq_nat t1' t2' 
    | Integer_Type t1', Integer_Type t2' => beq_nat t1' t2'
    | Array_Type t1', Array_Type t2' => beq_nat t1' t2'
    | Record_Type t1', Record_Type t2' => beq_nat t1' t2'
    | _, _ => false
    end.

  Definition is_in_mode (x: mode): bool := 
    match x with
    | In => true
    | _  => false
    end.

  Definition is_out_mode (x: mode): bool := 
    match x with
    | Out => true
    | _   => false
    end.

  Definition is_in_out_mode (x: mode): bool := 
    match x with
    | In_Out => true
    | _      => false
    end.

End LB_AuxiliaryFunctions.
