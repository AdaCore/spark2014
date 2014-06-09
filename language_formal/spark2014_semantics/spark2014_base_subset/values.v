(** 
_AUTHOR_

<<
Zhi Zhang
Departmnt of Computer and Information Sciences
Kansas State University
zhangzhi@ksu.edu
>>
*)

Require Export language.

(** * Value Types *) 

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


(** Type of basic values*)

(** TODO: now we only model the 32-bit singed integer for SPARK 
    program, where Coq integer (Z) is used to represent this integer  
    value with a range bound between min_signed and max_signed. 
    This integer range constraint is enforced when we define the
    semantics for the language;
*)
Inductive value : Type :=
    | Int (n : Z)
    | Bool (b : bool).

(** Type of stored values in the store *)
Inductive val: Type := 
    | Value: value -> val
    | Undefined: val.

(** Expression evaluation returns one of the following results:
    - normal values;
    - run time errors, which are required to be detected at run time,
      for example, overflow check and division by zero check;
    - abnormal values, which includes compile time errors
      (for example, type checks failure and undefined variables), 
      bounded errors and erroneous execution. In the future, 
      if it's necessary, we would refine the abnormal value into 
      these more precise categories (1.1.5);
*)
Inductive return_val: Type :=
    | Val_Normal: value -> return_val
    | Val_Run_Time_Error: return_val
    | Val_Abnormal: return_val. 

Inductive value_of_type: value -> type -> Prop :=
    | VT_Int: forall n, value_of_type (Int n) Integer
    | VT_Bool: forall b, value_of_type (Bool b) Boolean.


(** * Value Operations *)
Module Val.

(*
Notation "n == m" := (Zeq_bool n m) (at level 70, no associativity).
Notation "n != m" := (Zneq_bool n m) (at level 70, no associativity).
Notation "n > m" := (Z.gtb m n) (at level 70, no associativity).
Notation "n >= m" := (Z.geb m n) (at level 70, no associativity).
Notation "n < m" := (Z.ltb n m) (at level 70, no associativity).
Notation "n <= m" := (Z.leb n m) (at level 70, no associativity).
*)

(** ** Arithmetic operations *)

Definition add (v1 v2: value): return_val := 
    match v1, v2 with
    | Int v1', Int v2' => 
        Val_Normal (Int (v1' + v2'))
    | _, _ => Val_Abnormal
    end.

Definition sub (v1 v2: value): return_val := 
    match v1, v2 with
    | Int v1', Int v2' => Val_Normal (Int (v1' - v2'))
    | _, _ => Val_Abnormal
    end.

Definition mul (v1 v2: value): return_val :=
    match v1, v2 with
    | Int v1', Int v2' => Val_Normal (Int (v1' * v2'))
    | _, _ => Val_Abnormal
    end.


(** map Ada operators to corresponding Coq operators:
    - div -> Z.quot
    - rem -> Z.rem
    - mod -> Z.modulo

      (Note: Ada "mod" has the following formula in Why:    
       - if y > 0 then EuclideanDivision.mod x y else EuclideanDivision.mod x y + y)
*)

Definition div (v1 v2: value): return_val := 
    match v1, v2 with
    | Int v1', Int v2' => Val_Normal (Int (Z.quot v1' v2'))
    | _, _ => Val_Abnormal
    end.

Definition rem (v1 v2: value): return_val := 
    match v1, v2 with
    | Int v1', Int v2' => Val_Normal (Int (Z.rem v1' v2'))
    | _, _ => Val_Abnormal
    end.

(* the keyword "mod" cannot redefined here, so we use "mod'" *)
Definition mod' (v1 v2: value): return_val := 
    match v1, v2 with
    | Int v1', Int v2' => Val_Normal (Int (Z.modulo v1' v2'))
    | _, _ => Val_Abnormal
    end.

(** ** Logic operations  *)
Definition and (v1 v2: value): return_val :=
    match v1, v2 with
    | Bool v1', Bool v2' => Val_Normal (Bool (andb v1' v2'))
    | _, _ => Val_Abnormal
    end.

Definition or (v1 v2: value): return_val :=
    match v1, v2 with
    | Bool v1', Bool v2' => Val_Normal (Bool (orb v1' v2'))
    | _, _ => Val_Abnormal
    end.

(** ** Relational operations *)
Definition eq (v1 v2: value): return_val :=
    match v1, v2 with
    | Int v1', Int v2' => Val_Normal (Bool (Zeq_bool v1' v2'))
    | _, _ => Val_Abnormal
    end.

Definition ne (v1 v2: value): return_val :=
    match v1, v2 with
    | Int v1', Int v2' => Val_Normal (Bool (Zneq_bool v1' v2'))
    | _, _ => Val_Abnormal
    end.

Definition gt (v1 v2: value): return_val :=
    match v1, v2 with
    | Int v1', Int v2' => Val_Normal (Bool (Zgt_bool v1' v2'))
    | _, _ => Val_Abnormal
    end.

Definition ge (v1 v2: value): return_val :=
    match v1, v2 with
    | Int v1', Int v2' => Val_Normal (Bool (Zge_bool v1' v2'))
    | _, _ => Val_Abnormal
    end.

Definition lt (v1 v2: value): return_val :=
    match v1, v2 with
    | Int v1', Int v2' => Val_Normal (Bool (Zlt_bool v1' v2'))
    | _, _ => Val_Abnormal
    end.

Definition le (v1 v2: value): return_val :=
    match v1, v2 with
    | Int v1', Int v2' => Val_Normal (Bool (Zle_bool v1' v2'))
    | _, _ => Val_Abnormal
    end.

(** ** Unary operations *)
Definition not (v: value): return_val :=
    match v with
    | Bool v' => Val_Normal (Bool (negb v'))
    | _ => Val_Abnormal
    end.
End Val. 

 