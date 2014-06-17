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

Module Type ENTRY.
  Parameter T:Type.
End ENTRY.

Module STORE(V:ENTRY).

  Notation V:=V.T.

  Definition store : Type := list (idnum * V).

  Inductive first_occ {A B} : A -> B -> list (A*B) -> Prop :=
  | FO_Head: forall l a b, 
      first_occ a b ((a,b)::l)
  | FO_Tail: forall l a b a' b', 
      a<>a' -> 
      first_occ a b l -> 
      first_occ a b ((a',b')::l).

  Ltac wellf_rename_hyp th :=
    match th with
    | first_occ _ _ _ => fresh "h_firstocc"
    | _ => default_rename_hyp
    end.

  Ltac rename_hyp ::= wellf_rename_hyp.

  Lemma first_occ_det : forall A B l (a:A) (b b':B), 
    first_occ a b l -> 
      first_occ a b' l -> 
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
  Function resides (x : idnum) (s : store) := 
    match s with 
    | (y, v) :: s' =>
      if beq_nat x y then true else resides x s' 
    | nil => false
    end.

  (** fetch the value of x that has already been initialized in store *)
  Function fetches (x : idnum) (s : store): option V := 
    match s with 
    | (y, v) :: s' =>
      if beq_nat x y then Some v
      else fetches x s' 
    | nil => None
    end.

  (** [cut_to x s] return the pair (s',s'') where s = s' ++ s'' and s''
      starts with the first occurrence of [x] in [s]. If no occurrence
      of [x] exists in [s] then (nil,nil) is returned. *)
  Function cuts_to (x : idnum) (s : store): store*store := 
    match s with 
    | (y, v) :: s' =>
      (if beq_nat x y then (nil,s) 
       else let (l1,l2) := cuts_to x s' in
            (((y, v)::l1) , l2))
    | nil => (nil, nil)
    end.

  (** update the latest binding for x *)
  Function updates (s: store) (x : idnum) (v: V): option store := 
    match s with 
    | (y, v') :: s' => 
      if beq_nat x y then 
        Some ((y,v)::s') 
      else 
        match updates s' x v with
        | Some s'' => Some ((y,v')::s'')
        | None => None
        end
   | nil => None
   end.

  (** ** Lemmas about store operations *)
  Lemma fetches_in: forall x s v, 
    fetches x s = Some v -> first_occ x v s.
  Proof.
    intros x s.
    functional induction (fetches x s);
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
  Lemma in_fetches: forall x s v, 
    first_occ x v s -> 
      fetches x s = Some v.
  Proof.
    intros x s.
    functional induction (fetches x s);
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

  Lemma updates_in: forall s x v' s', 
    updates s x v' = Some s' -> 
      (exists v, first_occ x v s).
  Proof.
    intros s x v'.
    functional induction (updates s x v');
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
    
  Lemma in_updates: forall s x v' y v s',
    updates s x v' = Some s' ->
      first_occ y v s' ->
        ((y=x /\ v=v') \/ first_occ y v s).
  Proof.
    intros s x v'.
    functional induction (updates s x v'); simpl; intros y0 v0 s0 h h'; subst;
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


  Lemma updates_length: forall s x v s', 
    updates s x v = Some s' -> 
      List.length s = List.length s'.
  Proof.
    intros s x v.
    functional induction updates s x v;simpl
    ; intros updateds heq; inversion heq;clear heq
    ; subst;simpl;auto.
  Qed.



  (* The global stack is a stack of stores. One store per procedure
     currently running. *)
  Definition scope_level := nat. (* the scope level of the declared procedure to be called *)

  Definition frame := prod scope_level store.
  
  Definition level_of (f: frame) := fst f.

  Definition store_of (f: frame) := snd f.
  
  Definition stack := list frame.



  Definition reside (x: idnum) (f: frame) := resides x (store_of f).

  Definition fetch (x: idnum) (f: frame) := fetches x (store_of f).
  
  Definition cut_to (x: idnum) (f: frame) := cuts_to x (store_of f).

  Definition update (f: frame) (x: idnum) (v: V): option frame := 
    match updates (store_of f) x v with 
    | Some s => Some (level_of f, s)
    | None => None 
    end.
  
  Definition push (f: frame) (x: idnum) (v: V) := (level_of f, (x, v) :: (store_of f)).
  
  Definition newFrame (n: scope_level): frame := (n, nil). 

  (* split the stack into two substacks, scope levels of the first substack 
     equal or greater than n, and scope levels of another substack is less 
     than n;
  *)
  

  (** ** Stack properties *)
  (* TODO: rename this into MapsToG, and have inG of type idnum -> stack
     -> Prop + lamms between the two. *)
  Inductive inG: idnum -> V -> stack -> Prop := 
    | InG1: forall x v f s,
            first_occ x v (store_of f) -> inG x v (f :: s)
    | InG2: forall x v f s,
           (forall e, ~first_occ x e (store_of f)) -> inG x v s -> inG x v (f :: s).


  (* TODO: verifiy that x is not already bound in s? *)
  Definition pushG x v (s: stack) :=
    match s with
    | nil => None
    | f :: s' => Some ((push f x v) :: s')
    end.


  (** ** Stack operations *)
  Function fetchG (x : idnum) (s : stack) := 
    match s with 
    | f :: s' =>
      match fetch x f with
        | Some v => Some v
        | None => fetchG x s'
      end
    | nil => None
    end.

  Function updateG (s: stack) (x: idnum) (v: V): option stack := 
    match s with 
    | f :: s' =>
      match update f x v with
      | Some f' => Some (f' :: s')
      | None => match (updateG s' x v) with
                | Some s'' => Some (f :: s'')
                | None  => None
                end
      end
    | nil => None
    end.

  Function resideG (x : idnum) (s : stack) := 
    match s with 
    | f :: s' =>
      if reside x f then
        true
      else 
        resideG x s' 
    | nil => false
    end.

  Lemma fetch_in_none: forall x f, 
    fetch x f = None -> 
      forall v, ~first_occ x v (store_of f).
  Proof.
    intros x s. unfold fetch.
    functional induction fetches x (store_of s).
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

  Lemma fetchG_in_none: forall x s, 
    fetchG x s = None -> 
      forall v, ~inG x v s.
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
  Lemma fetchG_in: forall x s v, 
    fetchG x s = Some v -> 
      inG x v s.
  Proof.
    intros x s.
    functional induction (fetchG x s);
      intros v1 H;
      try match goal with
          | h: None = Some ?v |- _ => inversion h
          | h: Some ?v1 = Some ?v2 |- _ => inversion h; subst
          end; simpl.
    - apply fetches_in in e0.
      constructor 1.
      assumption.
    - constructor 2.
      + apply fetch_in_none.
        auto.
      + apply IHo.
        assumption.
  Qed.

  Lemma inG_fetchG: forall x s v, 
    inG x v s -> 
      fetchG x s = Some v.
  Proof.
    intros x s.
    functional induction (fetchG x s);
      intros v1 H;
      try match goal with
          | h: None = Some ?v |- _ => inversion h
          | h: Some ?v1 = Some ?v2 |- _ => inversion h; subst
          end; simpl.
    - apply fetches_in in e0.
      !inversion H;clear H.
      + rewrite (first_occ_det _ _ (store_of f) x v v1);auto.
      + destruct (H4 _ e0).
    - apply IHo.
      !inversion H.
      + pose (fetch_in_none _ _ e0 v1). contradiction.
      + assumption.
    - inversion H.
  Qed.


  Inductive stack_eq_length : stack -> stack -> Prop :=
    | eqnil: stack_eq_length nil nil
    | eqncons: forall s s' f f',
        stack_eq_length s s' ->
        List.length (store_of f) = List.length (store_of f') ->
        stack_eq_length (f :: s) (f' :: s').

  Lemma stack_eq_length_refl: forall s s', 
    s = s' -> 
      stack_eq_length s s'.
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

  Lemma stack_eq_length_sym: forall s s', 
    stack_eq_length s s' -> 
      stack_eq_length s' s.
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

  Lemma stack_eq_length_trans: forall s' s s'',
    stack_eq_length s s' ->
      stack_eq_length s' s'' -> 
        stack_eq_length s s''.
  Proof.
    intros s'.
    induction s';intros s s'' heq1 heq2
    ; try now (inversion heq1; inversion heq2;subst;constructor).
    inversion heq1.
    inversion heq2.
    subst.
    constructor.
    + apply IHs' ;assumption.
    + transitivity (List.length (store_of a));auto.
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

  Add Parametric Morphism: (@List.app frame)
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


  Lemma updateG_stack_eq_length: forall s x v s', 
    updateG s x v = Some s' -> 
      stack_eq_length s s'.
  Proof.
    admit.
  (*
    intros s x v.
    functional induction updateG s x v;simpl
    ; intros updateds heq; inversion heq;clear heq
    ; subst;simpl;auto.
    - constructor.
      + apply stack_eq_length_refl;auto.
      + unfold update in e0. eapply updates_length;eauto.
    - constructor.
      + apply IHo.
        assumption.
      + reflexivity.
  *)
  Qed.


  Lemma updateG_length: forall s x v s', 
    updateG s x v = Some s' -> 
      List.length s = List.length s'.
  Proof.
    intros s x v.
    functional induction updateG s x v;simpl
    ; intros updateds heq; inversion heq;clear heq
    ; subst;simpl;auto.
  Qed.

End STORE.

