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
Function fetch (x : idnum) (s : store): option val := 
    match s with 
    | (y, v) :: s' =>
      if beq_nat x y then
        match v with
        | Value _ => Some v
        | Procedure _ => Some v
        | Undefined => None
        end
      else fetch x s' 
    | nil => None
    end.

(** fetch the value of x that has already been initialized in store *)
Function cut_to (x : idnum) (s : store): store*store := 
  match s with 
    | (y, v) :: s' =>
      (if beq_nat x y then (nil,s) 
       else let (l1,l2) := cut_to x s' in
            (((y, v)::l1) , l2))
    | nil => (nil, nil)
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
    fetch x s = Some v -> List.In (x, v) s.
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


Lemma update_length:
  forall s x v s', update s x v = Some s' -> List.length s = List.length s'.
Proof.
  intros s x v.
  functional induction update s x v;simpl
  ; intros updateds heq; inversion heq;clear heq
  ; subst;simpl;auto.
Qed.

(** [UpdateList lid lv s s'] iff s' is s updated by the values in (combine lid lv). *)
Inductive UpdateList : list idnum -> list val -> store -> store -> Prop :=
| UpdateListnil: forall lid lv s, UpdateList lid lv s s
| UpdateListcons: forall id lid v lv s s' s'',
                    UpdateList lid lv s s'
                    -> update s' id v = Some s''
                    -> UpdateList (id::lid) (v::lv) s  s''.


(* The global stack is a stack of stores. One store per procedure
   currently running. *)
Definition stack := list store.

Function fetchG (x : idnum) (s : stack) := 
    match s with 
    | sto :: s' =>
      match fetch x sto with
          Some x => Some x
        | None => fetchG x s'
      end
    | nil => None
    end.

Function updateG (s : stack) (x : idnum) (v:val): option stack := 
  match s with 
    | sto :: s' =>
      match update sto x v with
          Some x => Some (x::s')
        | None => match (updateG s' x v) with
                      Some y => Some (sto::y)
                    | None  => None
                  end
      end
    | nil => None
  end.


Inductive InG: idnum -> val -> stack -> Prop := 
  InG1: forall x v (sto:store) (s:stack),
          List.In (x,v) sto -> InG x v (sto::s)
| InG2: forall x v (sto:store) (s:stack),
          InG x v s -> InG x v (sto::s).

(** ** Lemmas about stack operations *)
Lemma fetchG_in:
  forall x s v, 
    fetchG x s = Some v -> InG x v s.
Proof.
  intros x s.
  functional induction (fetchG x s);
    intros v1 H;
    try match goal with
          | h: None = Some ?v |- _ => inversion h
          | h: Some ?v1 = Some ?v2 |- _ => inversion h; subst
        end; simpl.
  - apply fetch_in in e0.
    constructor 1.
    assumption.
  - constructor 2.
    apply IHo.
    assumption.
Qed.

Inductive stack_eq_length : stack -> stack -> Prop :=
  eqnil: stack_eq_length nil nil
| eqncons: 
    forall l l' e e',
      stack_eq_length l l'
      -> List.length e = List.length e'
      -> stack_eq_length (e::l) (e'::l').


Lemma stack_eq_length_refl: forall s s', s = s' -> stack_eq_length s s'.
Proof.
  intros s.
  induction s;intros s' heq.
  - subst.
    constructor.
  - subst.
    constructor.
    + apply IHs.
      reflexivity.
    + reflexivity.
Qed.

Lemma stack_eq_length_sym: forall s s', stack_eq_length s s' -> stack_eq_length s' s.
Proof.
  intros s.
  induction s;intros s' heq.
  - inversion heq.
    constructor.
  - inversion heq.
    constructor.
    + apply IHs.
      assumption.
    + symmetry.
      assumption.
Qed.

Lemma stack_eq_length_trans:
  forall s' s s'',
    stack_eq_length s s'
    -> stack_eq_length s' s''
    -> stack_eq_length s s''.
Proof.
  intros s'.
  induction s';intros s s'' heq1 heq2
  ; try now (inversion heq1; inversion heq2;subst;constructor).
  inversion heq1.
  inversion heq2.
  subst.
  constructor.
  + apply IHs' ;assumption.
  + transitivity (List.length a);auto.
Qed.


Lemma updateG_stack_eq_length:
  forall s x v s', updateG s x v = Some s' -> stack_eq_length s s'.
Proof.
  intros s x v.
  functional induction updateG s x v;simpl
  ; intros updateds heq; inversion heq;clear heq
  ; subst;simpl;auto.
  - constructor.
    + apply stack_eq_length_refl;auto.
    + eapply update_length;eauto.
  - constructor.
    + apply IHo.
      assumption.
    + reflexivity.
Qed.


Lemma updateG_length:
  forall s x v s', updateG s x v = Some s' -> List.length s = List.length s'.
Proof.
  intros s x v.
  functional induction updateG s x v;simpl
  ; intros updateds heq; inversion heq;clear heq
  ; subst;simpl;auto.
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


