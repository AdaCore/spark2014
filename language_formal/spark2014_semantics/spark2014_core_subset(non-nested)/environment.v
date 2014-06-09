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

Module Type Entry.
  Parameter T:Type.
End Entry.

Module ENV(V:Entry).

Notation V:=V.T.

Definition store : Type := list (idnum * V).

Inductive FirstOcc {A B} : A -> B -> list (A*B) -> Prop :=
  FO_Here: forall l a b, FirstOcc a b ((a,b)::l)
| FO_Later: forall l a b a' b', a<>a' -> FirstOcc a b l -> FirstOcc a b ((a',b')::l).

Ltac wellf_rename_hyp th :=
    match th with
      | FirstOcc _ _ _ => fresh "h_firstocc"
      | _ => default_rename_hyp
    end.

Ltac rename_hyp ::= wellf_rename_hyp.

Lemma FirstOcc_det : forall A B l (a:A) (b b':B), 
                       FirstOcc a b l -> 
                       FirstOcc a b' l -> 
                       b = b'.
Proof.
  intros A B l a b b' h.  
  revert b'.
  !induction h;!intros.
  - !inversion h_firstocc.
    + reflexivity.
    + destruct H3. reflexivity.
  - apply IHh.
    !inversion h_firstocc.
    + destruct H. reflexivity.
    + assumption.
Qed.

(** ** Store operations *)
(** check whether variable x has already been declared *)
Function reside (x : idnum) (s : store) := 
  match s with 
    | (y, v) :: s' =>
      if beq_nat x y then true else reside x s' 
    | nil => false
  end.

(** fetch the value of x that has already been initialized in store *)
Function fetch (x : idnum) (s : store): option V := 
  match s with 
    | (y, v) :: s' =>
      if beq_nat x y then Some v
      else fetch x s' 
    | nil => None
  end.

(** [cut_to x s] return the pair (s',s'') where s = s' ++ s'' and s''
    starts with the first occurrence of [x] in [s]. If no occurrence
    of [x] exists in [s] then (nil,nil) is returned. *)
Function cut_to (x : idnum) (s : store): store*store := 
  match s with 
    | (y, v) :: s' =>
      (if beq_nat x y then (nil,s) 
       else let (l1,l2) := cut_to x s' in
            (((y, v)::l1) , l2))
    | nil => (nil, nil)
  end.

(** update the latest binding for x *)
Function update (s: store) (x : idnum) (v: V): option store := 
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
    fetch x s = Some v -> FirstOcc x v s.
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
    apply beq_nat_false_iff in e0.
    assumption.
    apply IHo.
    assumption.
Qed.

(** ** Lemmas about store operations *)
Lemma in_fetch: forall x s v, 
                  FirstOcc x v s -> fetch x s = Some v.
Proof.
  intros x s.
  functional induction (fetch x s);
    intros v1 H;
    try match goal with
    | h: None = Some ?v |- _ => inversion h
    | h: Some ?v1 = Some ?v2 |- _ => inversion h; subst
        end; simpl.
  - apply beq_nat_true_iff in e0; subst.
    !inversion H.
    + reflexivity.
    + destruct H4;auto.
  - apply IHo.
    !inversion H.
    + rewrite <- beq_nat_refl in e0.
      !inversion e0.
    + assumption. 
  - inversion H.
Qed.

Lemma update_in: forall s x v' s', 
    update s x v' = Some s' -> (exists v, FirstOcc x v s).
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
    right. 
    + apply beq_nat_false_iff in e0.
      assumption.
    + assumption.
Qed.
    
Lemma in_update: forall s x v' y v s',
                   update s x v' = Some s' ->
                   FirstOcc y v s'
                   -> ((y=x /\ v=v') \/ FirstOcc y v s).
Proof.
    intros s x v'.
    functional induction (update s x v'); simpl; intros y0 v0 s0 h h'; subst;
    (inversion h; clear h); subst.

  - apply beq_nat_true_iff in e0; subst.
    !inversion h'.
    + left. auto.
    + right.
      right;auto.
  - specialize (IHo y0 v0 s'' e1).
    !inversion h'.
    + right. left.
    + specialize (IHo h_firstocc). 
       destruct IHo as [h | h'']. subst.
      * left;auto.
      * right.
        right;auto.
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
Inductive UpdateList : list idnum -> list V -> store -> store -> Prop :=
| UpdateListnil: forall lid lv s, UpdateList lid lv s s
| UpdateListcons: forall id lid v lv s s' s'',
                    UpdateList lid lv s s'
                    -> update s' id v = Some s''
                    -> UpdateList (id::lid) (v::lv) s  s''.


(* The global stack is a stack of stores. One store per procedure
   currently running. *)
Definition stack := list store.

(** ** Stack properties *)
(* TODO: rename this into MapsToG, and have InG of type idnum -> stack
   -> Prop + lamms between the two. *)
Inductive InG: idnum -> V -> stack -> Prop := 
  InG1: forall x v (sto:store) (s:stack),
          FirstOcc x v sto -> InG x v (sto::s)
| InG2: forall x v (sto:store) (s:stack),
          (forall e, ~FirstOcc x e sto) -> InG x v s -> InG x v (sto::s).


(* TODO: verifiy that x is not already bound in s? *)
Definition addG x v (s:stack) :=
  match s with
    | nil => None
    | sto :: s' => Some (((x,v)::sto)::s')
  end.

(* TODO: verifiy that x is not already bound in s? *)
Inductive AddG : idnum -> V -> stack -> stack -> Prop :=
AddG1: forall id v sto st, AddG id v (sto::st) (((id,v)::sto)::st).

Lemma addg_AddG : forall id v st st', addG id v st = Some st' <-> AddG id v st st'.
Proof.
  intros id v st.
  !induction st; intros st'; simpl;split;intro h; try discriminate h;try now inversion h.
Qed.


(** ** Stack operations *)
Function fetchG (x : idnum) (s : stack) := 
    match s with 
    | sto :: s' =>
      match fetch x sto with
          Some x => Some x
        | None => fetchG x s'
      end
    | nil => None
    end.

Function updateG (s : stack) (x : idnum) (v:V): option stack := 
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

Function resideG (x : idnum) (s : stack) := 
    match s with 
    | sto :: s' =>
      if reside x sto then
        true
      else 
        resideG x s' 
    | nil => false
    end.

Lemma fetch_in_none:
  forall x s, 
    fetch x s = None -> forall v, ~FirstOcc x v s.
Proof.
  intros x s.
  functional induction fetch x s.
  - inversion 1.
  - apply beq_nat_false_iff in e0; subst.
    intros H v0.
    specialize (IHo H).
    intro abs.
    !inversion abs; clear abs.
    + destruct e0;auto.
    + destruct (IHo _ h_firstocc).
  - intros H v.
    intro abs.
    inversion abs.
Qed.

Lemma fetchG_in_none:
  forall x s, 
    fetchG x s = None -> forall v, ~InG x v s.
Proof.
  intros x s.
  functional induction fetchG x s.
  - inversion 1.
  - intros H v.
    intro abs.
    !inversion  abs.
    + pose (xxx:= fetch_in_none _ _ e0 v).
      clearbody xxx.
      contradiction.
    + specialize (IHo H v).
      contradiction.
  - intros H v.
    intro abs.
    inversion abs.
Qed.

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
    + apply fetch_in_none.
      auto.
    + apply IHo.
      assumption.
Qed.

Lemma inG_fetchG:
  forall x s v, 
    InG x v s -> fetchG x s = Some v.
Proof.
  intros x s.
  functional induction (fetchG x s);
    intros v1 H;
    try match goal with
          | h: None = Some ?v |- _ => inversion h
          | h: Some ?v1 = Some ?v2 |- _ => inversion h; subst
        end; simpl.
  - apply fetch_in in e0.
    !inversion H;clear H.
    + rewrite (FirstOcc_det _ _ sto x x0 v1);auto.
    + destruct (H4 _ e0).
  - apply IHo.
    !inversion H.
    + pose (fetch_in_none _ _ e0 v1). contradiction.
    + assumption.
  - inversion H.
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


Require Import Setoid.
Require Import Morphisms.

Lemma stack_eq_length_refl2: reflexive _ stack_eq_length.
Proof.
  hnf.
  intros x.
  apply stack_eq_length_refl.
  reflexivity.
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

Lemma stack_eq_length_trans2: transitive _ stack_eq_length.
Proof.
  hnf.
  intros x y z H H0.
  apply stack_eq_length_trans with (s':= y);auto.
Qed.
  



Add Parametric Relation: stack stack_eq_length
    reflexivity proved by stack_eq_length_refl2
    symmetry proved by stack_eq_length_sym
    transitivity proved by stack_eq_length_trans2
      as stack_eq_length_equiv_rel.

Add Parametric Morphism: (@List.app store)
    with signature stack_eq_length ==> stack_eq_length ==> stack_eq_length
      as app_morph_stack_eq_length.
Proof.
  intros x y H.
  induction H;simpl;intros.
  - assumption.
  - constructor 2.
    + apply IHstack_eq_length.
      assumption.
    + assumption.
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


Inductive cut_until: stack -> procnum -> stack -> stack -> Prop :=
  Cut_Until1: forall pname e s,
    reside pname e = true -> (* TODO: define an inductive here *)
    cut_until (e::s) pname nil (e::s)
| Cut_Until2: forall pname e s1 s2 s3,
    reside pname e = false -> (* TODO: define an inductive here *)
    cut_until s1 pname s2 s3 -> 
    cut_until (e::s1) pname (e::s2) s3.


Function cut_until_f s pbname :=
  match s with
    | nil => None
    | e::s' =>
      if reside pbname e then Some (nil,s)
      else
        match cut_until_f s' pbname with
          | None => None
          | Some (forget,called) => Some (e::forget , called)
        end
  end.


Lemma cut_until_correct : forall s pbname s' s'',
                            cut_until s pbname s' s'' -> cut_until_f s pbname = Some (s',s'').
Proof.
  intros s pbname s' s'' H.
  induction H;simpl.
  - rewrite H.
    reflexivity.
  - rewrite H.
    rewrite IHcut_until.
    reflexivity.
Qed.


Lemma cut_until_complete1 : forall s pbname s' s'',
                            cut_until_f s pbname = Some (s',s'')
                            -> cut_until s pbname s' s''.
Proof.
  intros s pbname.
  functional induction cut_until_f s pbname;simpl;intros s1 s2 H;try discriminate.
  - injection H.
    clear H.
    intros;subst.
    constructor 1.
    assumption.
  - injection H. clear H. intros ; subst.
    constructor 2.
    + assumption.
    + auto.
Qed.

Lemma cut_until_complete2 : forall s pbname s' s'',
                            cut_until_f s pbname = None
                            -> ~ cut_until s pbname s' s''.
Proof.
  intros s pbname s' s'' H.
  intro abs.
  apply cut_until_correct in abs.
  rewrite abs in H.
  discriminate.
Qed.

Lemma cut_until_def : forall s pbname s1 s2, cut_until s pbname s1 s2 -> s = s1++s2.
Proof.
  intros s pbname s1 s2 H.
  induction H.
  - reflexivity.
  - rewrite IHcut_until.
    reflexivity.
Qed.


Lemma cut_until_def2 : forall s pbname s1 s2,
                         cut_until s pbname s1 s2
                         -> (forall e, List.In e s1 -> reside pbname e = false).
Proof.
  intros s pbname s1 s2 H.
  induction H;intros.
  - inversion H0.
  - inversion H1; clear H1; subst.
    + assumption.
    + auto.
Qed.

Lemma cut_until_def3 : forall s pbname s1 s2 e s2',
                         cut_until s pbname s1 s2
                         -> s2 = e::s2'
                         -> reside pbname e = true.
Proof.
  intros s pbname s1 s2 e s2' H.
  revert e s2'.
  induction H;intros.
  - injection H0. clear H0; intros ; subst.
    assumption.
  - subst.
    apply IHcut_until with s2'.
    reflexivity.
Qed.


End ENV.

