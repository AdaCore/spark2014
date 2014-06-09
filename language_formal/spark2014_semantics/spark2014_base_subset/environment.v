(** 
_AUTHOR_

<<
Zhi Zhang
Departmnt of Computer and Information Sciences
Kansas State University
zhangzhi@ksu.edu
>>
*)

Require Export values.

(** for any valid variable x, it has an in/out mode, type and value 
    (either defined or undefined); as the in/out mode and type are
    invariant since the variable is declared, and they are used only
    at compile time, we keep these invariant information in a symbol 
    table called _symtb_; while the value of a variable will change 
    as the program executes, and it's used in run time evaluation, 
    so we keep this information in a store called _store_;
*)

(** * Store *)

(** ** Store as a list *)
(** it's a map from a variable, represented with natural number,
    to its value;
*)
Definition store : Type := list (idnum * val).

(** ** Store operations *)
(** check whether variable x has already been declared *)
Function reside (x : idnum) (s : store) := 
    match s with 
    | (y, v) :: s' =>
      if beq_nat x y then
        true
      else 
        reside x s' 
    | nil => false
    end.

(** fetch the value of x that has already been initialized in store *)
Function fetch (x : idnum) (s : store): option value := 
    match s with 
    | (y, v) :: s' =>
      if beq_nat x y then
        match v with
        | Value v => Some v
        | Undefined => None
        end
      else fetch x s' 
    | nil => None
    end.

(** update the latest binding for x *)
Function update (s: store) (x : idnum) (v: val): option store := 
    match s with 
    | (y, v') :: s' => 
      if beq_nat x y then 
        Some ((y,v)::s') 
      else 
        match update s' x v with
        | Some s'' => Some ((y,v')::s'')
        | None => None
        end
   | nil => None
   end.

(** ** Lemmas about store operations *)
Lemma fetch_in: forall x s v, 
    fetch x s = Some v -> List.In (x, Value v) s.
Proof.
    intros x s.
    functional induction (fetch x s);
    intros v1 H;
    try match goal with
    | h: None = Some ?v |- _ => inversion h
    | h: Some ?v1 = Some ?v2 |- _ => inversion h; subst
    end; simpl.
  - apply beq_nat_true_iff in e0; subst.
    left;auto.
  - right.
    apply IHo.
    assumption.
Qed.

Lemma update_in: forall s x v' s', 
    update s x v' = Some s' -> (exists v, List.In (x, v) s).
Proof.
    intros s x v'.
    functional induction (update s x v');
    intros s1 h1;
    try match goal with
    | h: None = Some ?s |- _ => inversion h
    | h: beq_nat _ _ = true |- _  => rewrite beq_nat_true_iff in h; subst
    end.
  - exists v'. 
    simpl.
    left; auto.
  - specialize (IHo s'' e1).
    inversion IHo.
    exists x0. simpl. 
    right; assumption.
Qed.
    
Lemma in_update: forall s x v' y v s',
                   update s x v' = Some s' ->
                   List.In (y, v) s'
                   -> ((y=x /\ v=v') \/ List.In (y,v) s).
Proof.
    intros s x v'.
    functional induction (update s x v'); simpl; intros y0 v0 s0 h h'; subst;
    (inversion h; clear h); subst.
    apply beq_nat_true_iff in e0; subst.
  - destruct h'.
    + left. inversion H; auto.
    + right. right; assumption.
  - specialize (IHo y0 v0 s'' e1).
    destruct h'.
    + right. left. assumption.
    + specialize (IHo H). 
       destruct IHo as [h | h'].
       *  left; assumption.
       * right. right; assumption.
Qed.


(** * Program State *)
(** Statement evaluation returns one of the following results:
    - normal state;
    - run time errors, which are required to be detected at run time,
      for example, overflow check and division by zero check;
    - unterminated state caused by infinite loop;
    - abnormal state, which includes compile time errors
      (for example, type checks failure and undefined variables), 
      bounded errors and erroneous execution. 
      In the future, the abnormal state can be refined into these 
      more precise categories (1.1.5);
*)

Inductive state: Type :=
    | S_Normal: store -> state
    | S_Run_Time_Error: state
    | S_Unterminated: state
    | S_Abnormal: state.
