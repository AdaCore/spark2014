Require Export language_basics.

(** * Run Time Error Types *)
Inductive error_type: Type :=
    | RTE_Division_By_Zero
    | RTE_Overflow
    | RTE_Index.   (* index check for an array access *)
(*  | RTE_Range *) (* range check for a scalar range, e.g. -1 is assigned to natural variable *)

(** * Return Values / States *)
(** Statement and expressions evaluation returns one of the following results:
    - normal result;
    - run time errors, which are required to be detected at run time,
      for example, overflow check and division by zero check;
    - unterminated state caused by infinite loop (only for functional semantics);
    - abnormal state, which includes compile time errors
      (for example, type checks failure and undefined variables), 
      bounded errors and erroneous execution. 
      In the future, the abnormal state can be refined into these 
      more precise categories (1.1.5);
*)

(* return value for exp/statement evaluation defined in inductive type *)
Inductive Return (A:Type): Type :=
    | Normal: A -> Return A
    | Run_Time_Error: error_type -> Return A.

(* return value for exp/statement evaluation defined in functional style *)
Inductive ReturnF (A:Type): Type :=
    | NormalV: Return A -> ReturnF A
    | Unterminated: ReturnF A
    | Abnormal: ReturnF A.

Arguments Normal [A] _.
Arguments Run_Time_Error [A] _.
Arguments NormalV [A] _.
Arguments Unterminated [A].
Arguments Abnormal [A].

(** the range of 32-bit (singed/unsigned) integer type: 
    - modulus : 2^32 ;
    - half_modulus : 2^31 ;
    - max_unsigned : 2^32 -1 ;
    - max_signed : 2^31 - 1 ;
    - min_signed : -2^31 ;
*)
Definition wordsize: nat := 32.
Definition modulus : Z := two_power_nat wordsize.
Definition half_modulus : Z := Z.div modulus 2.
Definition max_unsigned : Z := Z.sub modulus 1.
Definition max_signed : Z := Z.sub half_modulus 1.
Definition min_signed : Z := Z.opp half_modulus.

(** * Stored Values *) 

(** Type of basic values*)

(** TODO: now we only model the 32-bit singed integer for SPARK 
    program, where Coq integer (Z) is used to represent this integer  
    value with a range bound between min_signed and max_signed. 
    This integer range constraint is enforced when we define the
    semantics for the language;
*)

Inductive basic_value : Type :=
    | Int (n : Z)
    | Bool (b : bool).

Inductive aggregate_value : Type :=
    | ArrayV (a: (Z * Z) * (list (index * basic_value))) (* array value with lower and upper bound *)
    | RecordV (r: list (idnum * basic_value)).

(** Type of stored values in the store *)
Inductive value : Type :=
    | BasicV (v: basic_value)
    | AggregateV (v: aggregate_value)
    | Undefined.

(*
Inductive value_stored(Procedure_Decl: Type) (Type_Decl: Type): Type := 
    | Value (v:value)
    | Procedure (pd: Procedure_Decl)
    | TypeDef (td: Type_Decl)
    | Undefined.

Arguments Value [Procedure_Decl] [Type_Decl] _.
Arguments Procedure [Procedure_Decl] [Type_Decl] _.
Arguments TypeDef [Procedure_Decl] [Type_Decl] _.
Arguments Undefined [Procedure_Decl] [Type_Decl].
*)

Definition Division_Error: Return value := Run_Time_Error RTE_Division_By_Zero.
Definition Overflow_Error: Return value := Run_Time_Error RTE_Overflow.
Definition Index_Error: Return value := Run_Time_Error RTE_Index.


(** * Value Operations *)
Module Val.

(** ** Arithmetic Operations *)

Definition add (v1 v2: value): option value := 
    match v1, v2 with
    | BasicV (Int v1'), BasicV (Int v2') => Some (BasicV (Int (v1' + v2')))
    | _, _ => None
    end.

Definition sub (v1 v2: value): option value := 
    match v1, v2 with
    | BasicV (Int v1'), BasicV (Int v2') => Some (BasicV (Int (v1' - v2')))
    | _, _ => None
    end.

Definition mul (v1 v2: value): option value :=
    match v1, v2 with
    | BasicV (Int v1'), BasicV (Int v2') => Some (BasicV (Int (v1' * v2')))
    | _, _ => None
    end.


(** map Ada operators to corresponding Coq operators:
    - div -> Z.quot
    - rem -> Z.rem
    - mod -> Z.modulo

      (Note: Ada "mod" has the following formula in Why:    
       - if y > 0 then EuclideanDivision.mod x y else EuclideanDivision.mod x y + y)
*)

Definition div (v1 v2: value): option value := 
    match v1, v2 with
    | BasicV (Int v1'), BasicV (Int v2') => Some (BasicV (Int (Z.quot v1' v2')))
    | _, _ => None
    end.

Definition rem (v1 v2: value): option value := 
    match v1, v2 with
    | BasicV (Int v1'), BasicV (Int v2') => Some (BasicV (Int (Z.rem v1' v2')))
    | _, _ => None
    end.

(* the keyword "mod" cannot redefined here, so we use "mod'" *)
Definition mod' (v1 v2: value): option value := 
    match v1, v2 with
    | BasicV (Int v1'), BasicV (Int v2') => Some (BasicV (Int (Z.modulo v1' v2')))
    | _, _ => None
    end.

(** ** Logic Operations  *)
Definition and (v1 v2: value): option value :=
    match v1, v2 with
    | BasicV (Bool v1'), BasicV (Bool v2') => Some (BasicV (Bool (andb v1' v2')))
    | _, _ => None
    end.

Definition or (v1 v2: value): option value :=
    match v1, v2 with
    | BasicV (Bool v1'), BasicV (Bool v2') => Some (BasicV (Bool (orb v1' v2')))
    | _, _ => None
    end.

(** ** Relational Operations *)
Definition eq (v1 v2: value): option value :=
    match v1, v2 with
    | BasicV (Int v1'), BasicV (Int v2') => Some (BasicV (Bool (Zeq_bool v1' v2')))
    | _, _ => None
    end.

Definition ne (v1 v2: value): option value :=
    match v1, v2 with
    | BasicV (Int v1'), BasicV (Int v2') => Some (BasicV (Bool (Zneq_bool v1' v2')))
    | _, _ => None
    end.

Definition gt (v1 v2: value): option value :=
    match v1, v2 with
    | BasicV (Int v1'), BasicV (Int v2') => Some (BasicV (Bool (Zgt_bool v1' v2')))
    | _, _ => None
    end.

Definition ge (v1 v2: value): option value :=
    match v1, v2 with
    | BasicV (Int v1'), BasicV (Int v2') => Some (BasicV (Bool (Zge_bool v1' v2')))
    | _, _ => None
    end.

Definition lt (v1 v2: value): option value :=
    match v1, v2 with
    | BasicV (Int v1'), BasicV (Int v2') => Some (BasicV (Bool (Zlt_bool v1' v2')))
    | _, _ => None
    end.

Definition le (v1 v2: value): option value :=
    match v1, v2 with
    | BasicV (Int v1'), BasicV (Int v2') => Some (BasicV (Bool (Zle_bool v1' v2')))
    | _, _ => None
    end.

(** Unary Operations *)
Definition unary_not (v: value): option value :=
    match v with
    | BasicV (Bool v') => Some (BasicV (Bool (negb v')))
    | _ => None
    end.

Definition unary_plus (v: value): option value := 
    match v with
    | BasicV (Int v') => Some v
    | _ => None
    end.

Definition unary_minus (v: value): option value := 
    match v with
    | BasicV (Int v') => Some (BasicV (Int (Z.opp v')))
    | _ => None
    end.


(** * Binary Operations *)
Definition binary_operation (op: binary_operator) (v1: value) (v2: value): option value :=
    match op with
    | Equal => eq v1 v2
    | Not_Equal => ne v1 v2
    | Greater_Than => gt v1 v2
    | Greater_Than_Or_Equal => ge v1 v2
    | Less_Than => lt v1 v2
    | Less_Than_Or_Equal => le v1 v2
    | And => and v1 v2
    | Or => or v1 v2
    | Plus => add v1 v2
    | Minus => sub v1 v2
    | Multiply => mul v1 v2
    | Divide => div v1 v2
    end.

(** * Unary Operations *)
Definition unary_operation (op: unary_operator) (v: value): option value := 
    match op with
    | Not => unary_not v
    | Unary_Plus => unary_plus v
    | Unary_Minus => unary_minus v
    end. 

End Val. 

 
