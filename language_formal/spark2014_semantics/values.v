Require Export language.

Inductive value : Type :=
| Int (n : Z)
| Bool (b : bool).

(* type of stored values for variables in the stack *)
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
    | ValException: return_val.
(*    | ValAbnormal: return_val *) 

Inductive stored_value_type: val -> typ -> Prop :=
    | SVT_Int: forall n, stored_value_type (Value (Int n)) Tint
    | SVT_Bool: forall b, stored_value_type (Value (Bool b)) Tbool.

Inductive return_value_type: return_val -> typ -> Prop :=
    | EVT_Int: forall n, return_value_type (ValNormal (Int n)) Tint
    | EVT_Bool: forall b, return_value_type (ValNormal (Bool b)) Tbool.

(* Operations over values *)
Module Val.
  (* 1. Arithmetic operations *)

Notation "n == m" := (Zeq_bool n m) (at level 70, no associativity).
Notation "n != m" := (Zneq_bool n m) (at level 70, no associativity).
Notation "n <= m" := (Z.leb n m) (at level 70, no associativity).
Notation "n >= m" := (Z.geb m n) (at level 70, no associativity).
Notation "n < m" := (Z.ltb n m) (at level 70, no associativity).
Notation "n > m" := (Z.gtb m n) (at level 70, no associativity).

(* ToDo:  
    overflow checks for the following operations are needed to be done later
*)
Definition add (v1 v2: return_val): return_val := 
    match v1, v2 with
    | ValNormal n1, ValNormal n2 => 
          match n1, n2 with
          | Int n1', Int n2' => ValNormal (Int (n1' + n2'))
          | _, _ => ValException
          end
    | _, _ => ValException
    end.

Definition sub (v1 v2: return_val): return_val := 
    match v1, v2 with
    | ValNormal n1, ValNormal n2 => 
          match n1, n2 with
          | Int n1', Int n2' => ValNormal (Int (n1' - n2'))
          | _, _ => ValException
          end
    | _, _ => ValException
    end.

Definition mul (v1 v2: return_val): return_val :=
    match v1, v2 with
    | ValNormal n1, ValNormal n2 => 
          match n1, n2 with
          | Int n1', Int n2' => ValNormal (Int (n1' * n2'))
          | _, _ => ValException
          end
    | _, _ => ValException
    end.

(* ToDo: 
   check for division by zero 
*)
Definition div (v1 v2: return_val): return_val :=
    match v1, v2 with
    | ValNormal n1, ValNormal n2 => 
          match n1, n2 with
          | Int n1', Int n2' => ValNormal (Int (n1' / n2'))
          | _, _ => ValException
          end
    | _, _ => ValException
    end.

  (* 2. Logic operations  *)
Definition and (v1 v2: return_val): return_val :=
    match v1, v2 with
    | ValNormal b1, ValNormal b2 => 
          match b1, b2 with
          | Bool b1', Bool b2' => ValNormal (Bool (andb b1' b2'))
          | _, _ => ValException
          end
    | _, _ => ValException
    end.

Definition or (v1 v2: return_val): return_val :=
    match v1, v2 with
    | ValNormal b1, ValNormal b2 => 
          match b1, b2 with
          | Bool b1', Bool b2' => ValNormal (Bool (orb b1' b2'))
          | _, _ => ValException
          end
    | _, _ => ValException
    end.

  (* 3. Comparisons *)
Definition eq (v1 v2: return_val): return_val :=
    match v1, v2 with
    | ValNormal n1, ValNormal n2 => 
          match n1, n2 with
          | Int n1', Int n2' => ValNormal (Bool (n1' == n2'))
          | _, _ => ValException
          end
    | _, _ => ValException
    end.

Definition ne (v1 v2: return_val): return_val :=
    match v1, v2 with
    | ValNormal n1, ValNormal n2 => 
          match n1, n2 with
          | Int n1', Int n2' => ValNormal (Bool (n1' != n2'))
          | _, _ => ValException
          end
    | _, _ => ValException
    end.

  (* 4. Unary operations *)
Definition not (v: return_val): return_val :=
    match v with
    | ValNormal (Bool b) => ValNormal (Bool (negb b))
    | _ => ValException
    end.

End Val. 

 