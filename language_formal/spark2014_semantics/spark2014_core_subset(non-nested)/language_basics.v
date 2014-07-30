Require Export ZArith.
Require Export Coq.Lists.List.
Require Export Coq.Bool.Bool.
Require Export X_SparkTactics.
Require Export LibTactics.
Require Export more_list.
Require Export util.

(** This file defines basic data types and operations used in the abstract syntax trees *)

(** * Identifiers *)

(** Distinct AST number labeled for each AST node; it's not the part  
    of the SPARK language subset, it's introduced only for internal 
    use, for example, it can be used to locate the source of the errors,
    to collect type information for expression node, and to map ast node
    to its run time check flags and so on;
*)

Definition astnum := nat.

(** In CompCert, Cminor uses non-negative values to represent 
    identifiers, we follow this style by using natural numbers 
    to represent identifiers/names;
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

(** Note: now we only consider the 32-bit singed integer type for 
    our SPARK subset language, and model it with _Integer_; Actually,
    SPARK has various integer types, we can extend our types by 
    adding more SPARK types here and adding its corresponding value
    definition in values.v;
*)

Inductive type: Type :=
    | Boolean (* 3.5.3 *)
    | Integer (* 3.5.4 *)
    | Subtype (t: typenum) (* 3.2.2 *)
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

(** * Operations *)

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
