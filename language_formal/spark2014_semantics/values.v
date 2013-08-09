Require Export language.

(** * Value Types *)

(** Basic value type *)
Inductive value : Type :=
| Int (n : Z)
| Bool (b : bool).

(** Stored values type in the stack *)
Inductive val: Type := 
    | Value: value -> val
    | Vundef: val.

(* type of evaluation values 
   possible results:
     - normal evaluation results
     - non-well-formed errors 
       (type checks failure, undefined variables, un-initialized variables)
     - constraint-violated results (it's a security problem: overflow, division by zero)
*)
Inductive return_val: Type :=
    | ValNormal: value -> return_val
    | ValException: return_val
    | ValAbnormal: return_val. 

(** type of stored/return values *)
Inductive stored_value_type: val -> typ -> Prop :=
    | SVT_Int: forall n, stored_value_type (Value (Int n)) Tint
    | SVT_Bool: forall b, stored_value_type (Value (Bool b)) Tbool.

Inductive return_value_type: return_val -> typ -> Prop :=
    | RVT_Int: forall n, return_value_type (ValNormal (Int n)) Tint
    | RVT_Bool: forall b, return_value_type (ValNormal (Bool b)) Tbool.

Lemma value_type_consistent: forall v t,
    stored_value_type (Value v) t <-> return_value_type (ValNormal v) t.
Proof.
    intros; split; intros;
    destruct v; destruct t; 
    (try constructor; try inversion H).
Qed.

(** * Value Operations *)
Module Val.

Notation "n == m" := (Zeq_bool n m) (at level 70, no associativity).
Notation "n != m" := (Zneq_bool n m) (at level 70, no associativity).
Notation "n <= m" := (Z.leb n m) (at level 70, no associativity).
Notation "n >= m" := (Z.geb m n) (at level 70, no associativity).
Notation "n < m" := (Z.ltb n m) (at level 70, no associativity).
Notation "n > m" := (Z.gtb m n) (at level 70, no associativity).

(** ** Arithmetic operations *)
Definition add (v1 v2: value): return_val := 
    match v1, v2 with
    | Int v1', Int v2' => ValNormal (Int (v1' + v2'))
    | _, _ => ValAbnormal
    end.

Definition sub (v1 v2: value): return_val := 
    match v1, v2 with
    | Int v1', Int v2' => ValNormal (Int (v1' - v2'))
    | _, _ => ValAbnormal
    end.

Definition mul (v1 v2: value): return_val :=
    match v1, v2 with
    | Int v1', Int v2' => ValNormal (Int (v1' * v2'))
    | _, _ => ValAbnormal
    end.

Definition div (v1 v2: value): return_val :=
    match v1, v2 with
    | Int v1', Int v2' => ValNormal (Int (v1' / v2'))
    | _, _ => ValAbnormal
    end.

(** ** Logic operations  *)
Definition and (v1 v2: value): return_val :=
    match v1, v2 with
    | Bool v1', Bool v2' => ValNormal (Bool (andb v1' v2'))
    | _, _ => ValAbnormal
    end.

Definition or (v1 v2: value): return_val :=
    match v1, v2 with
    | Bool v1', Bool v2' => ValNormal (Bool (orb v1' v2'))
    | _, _ => ValAbnormal
    end.

(** ** Relational operations *)
Definition eq (v1 v2: value): return_val :=
    match v1, v2 with
    | Int v1', Int v2' => ValNormal (Bool (v1' == v2'))
    | _, _ => ValAbnormal
    end.

Definition ne (v1 v2: value): return_val :=
    match v1, v2 with
    | Int v1', Int v2' => ValNormal (Bool (v1' != v2'))
    | _, _ => ValAbnormal
    end.

(** ** Unary operations *)
Definition not (v: value): return_val :=
    match v with
    | Bool v' => ValNormal (Bool (negb v'))
    | _ => ValAbnormal
    end.
End Val. 

 