Require Export language.

(** * Value Types *)

(** uses CompCert’s 32-bit integer type *)
Definition wordsize: nat := 32.
Definition modulus : Z := two_power_nat wordsize.
Definition half_modulus : Z := Z.div modulus 2 (** modulus / 2 *).
Definition max_unsigned : Z := Z.sub modulus 1 (** modulus - 1 *).
Definition max_signed : Z := Z.sub half_modulus 1 (** half_modulus - 1 *).
Definition min_signed : Z := Z.opp half_modulus (** -half_modulus *).

(** Type of basic values *)
Inductive value : Type :=
    | Int (n : Z)
    | Bool (b : bool).

(** Type of stored values in the stack *)
Inductive val: Type := 
    | Value: value -> val
    | Undefined: val.

(** Expression evaluation returns one of the following results:
    - normal values;
    - run time errors, which is caught by run time checks,
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
    | Int v1', Int v2' => Val_Normal (Int (v1' + v2'))
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

Definition div (v1 v2: value): return_val :=
    match v1, v2 with
    | Int v1', Int v2' => Val_Normal (Int (v1' / v2'))
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

 