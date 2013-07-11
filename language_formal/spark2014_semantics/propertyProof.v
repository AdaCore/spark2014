Require Export util.
Require Export wellformedness.
Require Export semantics.

(** * Properties Proof *)

(** some help tactics used to prove lemmas *)
Ltac simpl_binop_hyp :=
    repeat match goal with
    | [h: Some ?T = binop_type ?OP ?T1 ?T1 |- _ ] => 
            unfold binop_type in h; simpl in h; inversion h; subst
    | [h: binop_type ?OP ?T1 ?T1 = Some ?T |- _ ] => 
            unfold binop_type in h; simpl in h; inversion h; subst
    | [h: ValNormal ?V = eval_binop ?OP (ValNormal _) (ValNormal _) |- _] =>
            unfold eval_binop in h; simpl in h; inversion h; subst
    | [h: eval_binop ?OP (ValNormal _) (ValNormal _) = ValNormal ?V |- _] =>
            unfold eval_binop in h; simpl in h; inversion h; subst
    end.


Ltac rm_wt_expr :=
    repeat match goal with
    | [ |- well_typed_expr _ (Evar _ _) _] => apply WT_Evar
    | [ |- well_typed_expr _ (Eunop _ _ _) _] => eapply WT_Eunop
    | [ |- well_typed_expr _ (Ebinop _ ?OP ?E1 ?E2) ?T] => eapply WT_Ebinop (* it will generate some universal variables *)
    | [ h: well_typed_expr _ ?E ?T |- well_typed_expr _ ?E _ ] => apply h 
    | [ |- context[binop_type _ _ _]] => unfold binop_type; auto
    end.


Ltac rm_contradict := 
    match goal with
    | [h: return_value_type ValException Tint |- _ ] =>  inversion h
    | [h: return_value_type ValException Tbool |- _ ] =>  inversion h
    | [h: return_value_type (ValNormal (Bool _)) Tint |- _ ] =>  inversion h
    | [h: return_value_type (ValNormal (Int _)) Tbool |- _ ] =>  inversion h
    | [h: Some ?T = binop_type ?OP Tint Tbool |- _ ] => unfold binop_type in h; simpl in h; inversion h
    | [h: Some ?T = binop_type ?OP Tbool Tint |- _ ] => unfold binop_type in h; simpl in h; inversion h
    end.

(** the type of the expression evaluation result should be consistent with the type  
     computed by the type checker
*)
Lemma eval_type_reserve: forall tb s e v t,
    type_check_stack tb s -> 
    eval_expr s e (ValNormal v) ->
    well_typed_expr tb e t ->
    return_value_type (ValNormal v) t.
Proof.
    intros tb s e.
    induction e;
    intros v t h1 h2 h3;
    inversion h3;
    inversion h2; subst.
  - (* Econst *)
    inversion H7; subst.
    constructor.
  - inversion H7; subst.
    constructor.  
  - (* Evar *)
    specialize (typed_value _ _ i v h1 ); intros hz1.
    specialize (hz1 H6).
    rm_exists.
    rewrite H3 in H. inversion H; subst.
    apply value_type_consistent; assumption.
  - (* Ebinop *)
    specialize (IHe1 _ _ h1 H12 H5).
    specialize (IHe2 _ _ h1 H14 H6).
    destruct v1 as [v11 | v12]; inversion IHe1; subst;
    destruct v2 as [v21 | v22]; try rm_contradict.
    + destruct b; 
       repeat simpl_binop_hyp; 
       simpl; try constructor.
       destruct (Zeq_bool v21 0).
       * inversion H0.
       * constructor.       
    + destruct b; try simpl_binop_hyp;
       constructor.
  - (* Eunop *)
    rewrite <- H8.
    destruct op; destruct v0; inversion H8.
    constructor.
Qed.

(** the type of the expression evaluation result by eval_expr_with_checks should be 
     consistent with the type computed by the type checker;
     the difference between eval_expr and eval_expr_with_checks is that:
     eval_expr has checks performed implicitly according to the language semantics, while
     eval_expr_with_checks performs checks only if there are check flags requiring to do that
*)
Lemma eval_type_reserve2: forall tb s cks e v t,
    type_check_stack tb s -> 
    eval_expr_with_checks cks s e (ValNormal v) ->
    well_typed_expr tb e t ->
    return_value_type (ValNormal v) t.
Proof.
    intros tb s cks e.
    induction e;
    intros v t h1 h2 h3;
    inversion h3;
    inversion h2; subst.
  - (* Econst *)
    inversion H7; subst.
    constructor.
  - inversion H7; subst.
    constructor.  
  - (* Evar *)
    specialize (typed_value _ _ i v h1 ); intros hz1.
    specialize (hz1 H6).
    rm_exists.
    rewrite H3 in H. inversion H; subst.
    apply value_type_consistent; assumption.
  - (* Ebinop *)
    specialize (IHe1 _ _ h1 H12 H5).
    specialize (IHe2 _ _ h1 H13 H6).
    destruct v1 as [v11 | v12]; inversion IHe1; subst;
    destruct v2 as [v21 | v22]; try rm_contradict.
    + destruct b; 
       repeat simpl_binop_hyp; 
       simpl; try constructor.
       destruct (Zeq_bool v21 0).
       * inversion H0.
       * constructor.       
    + destruct b; try simpl_binop_hyp;
       constructor.
  - (* Eunop *)
    rewrite <- H8.
    destruct op; destruct v0; inversion H8.
    constructor.
Qed.

(**************************************************************************)
(**************************************************************************)

(** some help lemmas *)
Lemma valid_update: forall tb s ast_id x e v,
    type_check_stack tb s ->
    well_typed_stmt tb (Sassign ast_id x e) ->
    exists s', update s x (Value v) = Some s'.
Proof.
    intros tb s ast_id x e v h1 h2.
    inversion h2; subst.
    specialize (typed_value' _ _ _ Out t h1 H2); intros hz1.
    rm_exists.
    clear h1 h2 H0 H2 H4.
    functional induction (reside x s).
    + unfold update; rewrite e1.
       exists ((y, Value v) :: s'); auto.
    + specialize (IHb H).
       rm_exists.
       unfold update.
       rewrite e1.
       fold update.
       rewrite H0. 
       exists ((y, v0) :: x0); auto.
    + inversion H.
Qed.

(** update to the well-typed stack should return well-typed stack  *)
Lemma type_reserve: forall s x v s' tb m t ,
    update s x (Value v) = Some s' ->    
    type_check_stack tb s -> 
    lookup x tb = Some (m, t)-> 
    return_value_type (ValNormal v) t ->
    type_check_stack tb s'.
Proof.
    intros s x v.
    remember (Value v) as v'0.
    functional induction (update s x v'0);
    intros s'0 tb m t h1 h2 h3 h4.
  - inversion h1; clear h1; subst.
    destruct tb. 
    + inversion h3.
    + destruct p.
       inversion h2; subst;
       unfold lookup in h3; rewrite e0 in h3; fold lookup;
       inversion h3; clear h3; subst;
       destruct v;
       [ rm_contradict | | | rm_contradict | rm_contradict | | | rm_contradict ];
       constructor; assumption.
  - inversion h1; subst.
    destruct tb.
    + inversion h3.
    + assert (hz1: Value v = Value v); auto.
       destruct p; 
       inversion h2; subst;
       constructor;
       unfold lookup in h3; rewrite e0 in h3; fold lookup in h3;
       specialize (IHo hz1 _ _ _ _ e1 H0 h3 h4);
       assumption.
  - inversion h1.
  - inversion h1.
Qed.

(** the resulting stack should be well-typed after the modification to the initially well-typed stack by the assignment *)
Lemma type_reserve_assign: forall tb s ast_id x e v s',
    type_check_stack tb s -> 
    well_typed_stmt tb (Sassign ast_id x e) -> 
    eval_expr s e (ValNormal v) ->
    update s x (Value v) = Some s' ->
    type_check_stack tb s'. 
Proof.
    intros tb s ast_id x e v s' h1 h2 h3 h4.
    inversion h2; subst.
    specialize (eval_type_reserve _ _ _ _ _ h1 h3 H4); intros hz1.
    specialize (type_reserve _ _ _ _ _ _ _ h4 h1 H2 hz1); intros hz2.
    assumption.
Qed.

(** the resulting state for executing a statement can be either exception or a 
     normal state according to the semantics rules 
*)
Lemma symbol_consistent_reserve_0: forall tb s c s',
    type_check_stack tb s -> 
    well_typed_stmt tb c ->
    eval_stmt s c s' -> 
    s' = SException \/ (exists s0, s' = SNormal s0 /\ type_check_stack tb s0).
Proof.
    intros tb s c s' h1 h2 h3.
    induction h3;
    try match goal with
    | [ |- SException = SException \/ _ ] => left; reflexivity
    end.
  - (* Sassign *)
    right.
    exists s1.
    split.
    reflexivity.
    specialize (type_reserve_assign _ _ _ _ _ _ _ h1 h2 H H0); intros hz1.
    assumption.
  - (* Sseq *)
    inversion h2; subst.
    specialize (IHh3_1 h1 H2).
    destruct IHh3_1 as [hz1 | hz1]; inversion hz1.
    destruct H. 
    inversion H; subst.
    specialize (IHh3_2 H0 H4).
    assumption.
  - (* Sifthen_true *)
    inversion h2; subst.
    apply IHh3; assumption.
  - (* Sifthen_false *)
    right. 
    exists s;
    split; auto.
  - (* Swhile_true *)
    apply IHh3_2; auto.
    inversion h2; subst.
    specialize (IHh3_1 h1 H5).
    destruct IHh3_1 as [hz1 | hz1]; inversion hz1.
    destruct hz1. destruct H0.
    inversion H0; subst. 
    assumption.
  - (* Swhile_false *)
    right.
    exists s; 
    split; auto.
Qed.

(** 
    if the initial stack is well-typed, and when we execute a command, 
    the resulting normal stack should also be well-typed
*)
Lemma symbol_consistent_reserve: forall tb s c s',
    type_check_stack tb s -> 
    well_typed_stmt tb c ->
    eval_stmt s c (SNormal s') -> 
    type_check_stack tb s'. 
Proof.
    intros tb s c s' h1 h2 h3.
    remember (SNormal s') as s1.
    specialize (symbol_consistent_reserve_0 _ _ _ _ h1 h2 h3); intros hz1.
    subst.
    destruct hz1 as [hz2 | hz2]; inversion hz2.
    destruct H.
    inversion H; subst.
    assumption.
Qed.


(** for any stack s, a corresponding initialization state map can be computed from it *)
Lemma imap_exists: forall s, 
    exists istate, initializationMap s istate.
Proof.
    intros s.
    induction s.
    exists nil; constructor.
    rm_exists.
    destruct a.
    destruct v.
  - exists ((i, Init) :: x); constructor. 
    intuition. inversion H0.
    assumption.
  - exists ((i, Uninit) :: x); constructor.
    auto.
    assumption.
Qed.

(****************************************************)
(****************************************************)

(** 
    if expression e is well-defined (meaning that all variables used in e has been initialized) under the 
    initialization state map istate1, and for all variables that are initialized in istate1 are also initialized in istate2, 
    then of course, e is also well-typed under istate2
*)
Lemma initializationMap_expr: forall istate1 e istate2,
     well_defined_expr istate1 e ->   
     (forall x, fetch2 x istate1 = Some Init -> fetch2 x istate2 = Some Init) ->
     well_defined_expr istate2 e.
Proof.
    intros istate1 e istate2 h1.
    generalize istate2. 
    clear istate2.
    induction e;
    intros istate2 h2.
  - destruct c; constructor.
  - inversion h1; subst.
    specialize (h2 _ H1).
    constructor. assumption.
  - inversion h1; subst.
    constructor.
    + specialize (IHe1 H2 _ h2).
       assumption.
    + specialize (IHe2 H5 _ h2).
       assumption.
  - inversion h1; subst.
    constructor.
    specialize (IHe H1 _ h2).
    assumption.
Qed.

(* this modified version is used to prove lemma: ''initializationMap_stmt'' *)
(** 
    if expression e is well-defined (meaning that all variables used in e has been initialized) under the 
    initialization state map istate1, and for all variables that are initialized in istate1 are also initialized in istate2, 
    and for variables that are uninitialized in state1 may be initialized or uninitialized in istate2,
    then of course, e is also well-typed under istate2
*)
Lemma initializationMap_expr1: forall istate1 e istate2,
     well_defined_expr istate1 e ->   
     (forall x, (fetch2 x istate1 = Some Init -> fetch2 x istate2 = Some Init) /\
                   (fetch2 x istate1 = Some Uninit -> exists m, fetch2 x istate2 = Some m)) ->
     well_defined_expr istate2 e.
Proof.
    intros.
    distr_qualifier.
    specialize (initializationMap_expr _ _ _ H H0); intros hz1.
    assumption.
Qed.

(** 
    if istate1 is a subset of istate2, which means that all variables that are initialized in istate1 are also
    initialized in istate2, and istate2 is a subset of istate3, then istate1 is subset of istate3 
*)
Lemma fetch2_transitive: forall istate1 istate2 istate3,
    (forall x : idnum,
      (fetch2 x istate1 = Some Init -> fetch2 x istate2 = Some Init) /\
      (fetch2 x istate1 = Some Uninit ->
       exists m : init_mode, fetch2 x istate2 = Some m)) ->       
    (forall x : idnum,
      (fetch2 x istate2 = Some Init -> fetch2 x istate3 = Some Init) /\
      (fetch2 x istate2 = Some Uninit ->
       exists m : init_mode, fetch2 x istate3 = Some m)) ->
    (forall x : idnum,
      (fetch2 x istate1 = Some Init -> fetch2 x istate3 = Some Init) /\
      (fetch2 x istate1 = Some Uninit ->
       exists m : init_mode, fetch2 x istate3 = Some m)).
Proof.
    intros istate1 istate2 istate3 h1 h2.
    intros x.
    repeat distr_qualifier.
    split; intros hz1.
  - apply H0.
    apply H2; assumption.
  - specialize (H3 _ hz1).
    rm_exists.
    destruct x0 as [x1 | x2].
    + specialize (H0 _ H).
       exists Init; assumption.
    + specialize (H1 _ H).
       assumption.
Qed.

(* 'c' is put before 'istate1', because when we do induction on 'c', keep 'istate1' universal *)
(** 
    if command c is well-defined under both the initialization states istate1 and istate2 and 
    istate1 is a subset of istate2, then the resulting initialization state istate1' should be the subset 
    of istate2'
*)
Lemma wd_fetch2_sync: forall c istate1 istate1' istate2 istate2',
    well_defined_stmt istate1 c istate1' ->
    well_defined_stmt istate2 c istate2' ->
    (forall x, (fetch2 x istate1 = Some Init -> fetch2 x istate2 = Some Init) /\
                  (fetch2 x istate1 = Some Uninit -> exists m', fetch2 x istate2 = Some m')) ->
    (forall x, (fetch2 x istate1' = Some Init -> fetch2 x istate2' = Some Init) /\
                  (fetch2 x istate1' = Some Uninit -> exists m', fetch2 x istate2' = Some m')).
Proof.
    induction c;
    intros istate1 istate1' istate2 istate2' h1 h2 h3.
  - distr_qualifier.
    inversion h1; subst.
    inversion h2; subst.
    intros x.
    split; intros hz1.
    + specialize (update2_in1 _ _ _ _ _ _ H7 hz1); intros hz2.
       inversion hz2 as [hz3 | hz4].
       * inversion hz3; subst.
         specialize (update2_fetch2_new _ _ _ _  H9). 
         auto.
       * rm_exists.
         specialize (H0 _ H2).
         specialize (update2_fetch2_old _ _ _ _ _ H9 H); intros hz3.
         rewrite H0 in hz3.
         assumption.
    + specialize (update2_in1 _ _ _ _ _ _ H7 hz1); intros hz2.
       inversion hz2 as [hz3 | hz4].
       * inversion hz3.
          inversion H2.
       * rm_exists.
         specialize (H1 _ H2).
         specialize (update2_fetch2_old _ _ _ _ _ H9 H); intros hz3.
         rewrite hz3.
         assumption.
  - distr_qualifier.
    inversion h1; subst.
    inversion h2; subst.
    intros x.
    split; intros hz1.
    specialize (H0 _ hz1); assumption.
    specialize (H1 _ hz1); assumption.
  - distr_qualifier.
    inversion h1; subst.
    inversion h2; subst.
    intros x.
    split; intros hz1.
    specialize (H0 _ hz1); assumption.
    specialize (H1 _ hz1); assumption.
  - inversion h1; subst.
    inversion h2; subst.
    intros x.
    split; intros hz1;
    specialize (IHc1 _ _ _ _ H4 H6 h3);
    specialize (IHc2 _ _ _ _ H5 H7 IHc1);
    repeat distr_qualifier.
    + apply H2. assumption.
    + apply H3. assumption.
Qed.

(** 
    if command c is well-defined under the initialization state istate1, and istate1 is a subset of  
    istate2, then c should also be well-defined under istate2
*)
Lemma initializationMap_stmt: forall istate1 c istate1' istate2,
     well_defined_stmt istate1 c istate1' ->   
     (forall x, (fetch2 x istate1 = Some Init -> fetch2 x istate2 = Some Init) /\
                   (fetch2 x istate1 = Some Uninit -> exists m, fetch2 x istate2 = Some m)) ->
     exists istate2', well_defined_stmt istate2 c istate2'.
Proof.
    intros istate1 c istate1' istate2 h1.
    generalize istate2. clear istate2.
    induction h1;
    intros istate2 h2.
  - specialize (initializationMap_expr1 _ _ _ H h2); intros hz1.
    assert (hz2: exists istate, update2 istate2 x Init = Some istate).
    + distr_qualifier.
       specialize (update2_fetch2 _ _ _ _ H0); intros hz2.
       rm_exists. 
       destruct x0.
       * specialize (H2 _ H1).
         specialize (fetch2_update2 _ _ _ Init H2); intros hz3.
         assumption.
       * specialize (H3 _ H1).
         inversion H3.
         specialize (fetch2_update2 _ _ _ Init H4); intros hz4.
         assumption.
    + rm_exists.
       exists x0.
       constructor; assumption.
  - specialize (IHh1_1 _ h2).
    rm_exists.
    assert (hz2: forall y : idnum, (fetch2 y s' = Some Init -> fetch2 y x = Some Init) /\ 
                                                 (fetch2 y s' = Some Uninit -> exists m', fetch2 y x = Some m')).
    + specialize (wd_fetch2_sync _ _ _ _ _ h1_1 H h2); intros hz1.
       assumption.
    + specialize (IHh1_2 x hz2).
       rm_exists.
       exists x0.
       apply WD_Sseq with (s' := x);
       assumption.
  - exists istate2.
    specialize (IHh1 _ h2).
    rm_exists.
    apply WD_Sifthen with (s' := x).    
    + distr_qualifier.
       specialize (initializationMap_expr _ _ _ H H2); intros hz1.
       assumption.
    + assumption.
  - exists istate2.
    specialize (IHh1 _ h2).
    rm_exists.
    apply WD_Swhile with (s' := x).
    + distr_qualifier.
       specialize (initializationMap_expr _ _ _ H H2); intros hz1.
       assumption.
    + assumption.
Qed.

(** 
    command may change the uninitialized variables into initialized ones, 
    so the initialization state istate before executing command c should be
    subset of the resulting initialization state istate'
*)
Lemma initializationMap_inc: forall istate c istate',
     well_defined_stmt istate c istate' ->   
     (forall x, (fetch2 x istate = Some Init -> fetch2 x istate' = Some Init) /\
                   (fetch2 x istate = Some Uninit -> exists m, fetch2 x istate' = Some m)).
Proof.
    intros istate c istate' h1.
    induction h1; 
    intros x0.
  - split; intros;
    remember (beq_nat x0 x) as eq;
    symmetry in Heqeq;
    destruct eq as [eq1 | eq2].
       * apply beq_nat_true in Heqeq.
         subst.
         specialize (update2_fetch2_new _ _ _ _ H0); intros hz1.
         assumption.
       * apply beq_nat_false in Heqeq.
         specialize (update2_fetch2_old _ _ _ _ _ H0 Heqeq); intros hz1.
         rewrite hz1.
         assumption.
       * apply beq_nat_true in Heqeq.
         subst.
         specialize (update2_fetch2_new _ _ _ _ H0); intros hz1.
         exists Init; assumption.
       * apply beq_nat_false in Heqeq.
         specialize (update2_fetch2_old _ _ _ _ _ H0 Heqeq); intros hz1.
         rewrite hz1.
         exists Uninit; assumption.         
  - repeat distr_qualifier.
    split; intros hz1.
    + apply H0.
       apply H2.
       assumption.
    + specialize (H3 _ hz1).
       rm_exists.
       destruct x.
       specialize (H0 _ H).
       exists Init; assumption.
       specialize (H1 _ H).
       assumption.
  - split.
    + auto.
    + intros.
       exists Uninit.
       assumption.
  - split.
    + auto.
    + intros.
       exists Uninit.
       assumption.
Qed.

Ltac rm_hyps := 
    match goal with
    | [ h: SNormal _ = SException \/ _ |- _] => destruct h as [h1z | h2z]; [inversion h1z | intuition] 
    end.

(** 
    in well_defined_stmt, the initialization state istate' after executing the conditional and while statement is 
    defined as the intersection of the resulting initialization states from both branches;
    in eval_stmt, it executes either true branch or false branch for conditional and while statemet according
    to the current state s,  so the initialization state istate1 computed from s' should be a superset of istate'
 *)
Lemma eval_stmt_greater_0: forall s c s' istate istate' s0 istate1,
     eval_stmt s c s' ->
     initializationMap s istate ->
     well_defined_stmt istate c istate' -> 
     s' = SException \/ 
     (s' = SNormal s0 /\ initializationMap s0 istate1 -> 
     (forall x, (fetch2 x istate' = Some Init -> fetch2 x istate1 = Some Init) /\
                   (fetch2 x istate' = Some Uninit -> exists m, fetch2 x istate1 = Some m))).
Proof.
    intros s c s' istate istate' s0 istate1 h1.
    generalize istate istate' s0 istate1.
    clear istate istate' s0 istate1.
    induction h1;
    intros istate istate' s0 istate1 h2 h3;
    try match goal with
    | [ |- SException = SException \/ _ ] => left; reflexivity
    end.
  - (* 1. Sassign *)
    right; intros h4.
    inversion h3; subst.
    destruct h4.
    inversion H1; subst.
    specialize (update_consis _ _ _ _ _ _ _ h2 H0 H7 H2); intros hz1.
    subst.
    intros. 
    split; intros.
    + assumption.
    + exists Uninit.
       assumption.
  - (* 2. Sseq *)
    inversion h3; subst.
    specialize (imap_exists s1); intros hz1.
    rm_exists.
    specialize (IHh1_1 _ _ s1 x h2 H4).
    rm_hyps.
    assert (hz2: exists istate, well_defined_stmt x c2 istate).
    specialize (initializationMap_stmt _ _ _ _ H5 H0); intros hz2.
    assumption.
    rm_exists.
    specialize (IHh1_2 _ _ s0 istate1 H H1).
    intuition. right.
    intros H2. destruct H2.
    specialize (H3 H2 H6).
    specialize (wd_fetch2_sync _ _ _ _ _ H5 H1 H0); intros hz3.
    specialize (fetch2_transitive _ _ _ hz3 H3); intros hz4.
    assumption.
  - (* 3. Sifthen_true *)
    inversion h3; subst.
    specialize (IHh1 _ _ s0 istate1 h2 H6).
    specialize (initializationMap_inc _ _ _ H6); intros hz1.
    destruct IHh1. left; assumption.
    right; intros H2.
    specialize (H0 H2).
    specialize (fetch2_transitive _ _ _ hz1 H0); intros hz2.
    assumption.
  - (* 4. Sifthen_false *)
    inversion h3; subst.
    right; intros H2.
    destruct H2. inversion H0; subst.
    specialize (initializationMap_unique _ _ _ H1 h2); intros hz3.
    subst. 
    intuition. 
    exists Uninit; auto.
  - (* 5. Swhile_true *)
    inversion h3; subst.
    specialize (imap_exists s1); intros hz1.
    rm_exists.
    specialize (IHh1_1 _ _ s1 x h2 H6).
    specialize (initializationMap_inc _ _ _ H6); intros hz2.
    assert (hz2': exists istate, well_defined_stmt x (Swhile ast_id b c) istate).
    exists x.
    assert (hz3: exists istate, well_defined_stmt x c istate).
    specialize (initializationMap_stmt _ _ _ _ H6 hz2); intros hz3.
    inversion hz3.
    rm_hyps.
    specialize (initializationMap_stmt _ _ _ _ H1 H2); intros hz4.    
    assumption.
    inversion hz3.
    apply WD_Swhile with (s' := x0). 
    + rm_hyps.
       specialize (fetch2_transitive _ _ _ hz2 H2); intros hz5.
       specialize (initializationMap_expr1 _ _ _ H5 hz5); intros hz6.
       assumption.
    + assumption.
    + inversion hz2'.
       inversion H1; subst.
       specialize (IHh1_2 _ _ s0 istate1 H0 H1).
       destruct IHh1_2. left; assumption.
       right; intros H3. 
       specialize (H2 H3).
       destruct IHh1_1. inversion H4.
       assert (hz5: SNormal s1 = SNormal s1 /\ initializationMap s1 x0).
       split; auto.
       specialize (H4 hz5).
       specialize (fetch2_transitive _ _ _ H4 H2); intros hz3.
       specialize (fetch2_transitive _ _ _ hz2 hz3); intros hz4.
       assumption.
  - (* 6. Swhile_false *)
    inversion h3; subst.
    right; intros.
    destruct H0. inversion H0; subst.
    specialize (initializationMap_unique _ _ _ H1 h2); intros hz3.
    subst.
    split; intuition.
    exists Uninit; auto.
Qed.

(** 
    it's similar to eval_stmt_greater_0, the only difference is that we exclude the
    exception state when running eval_stmt here 
*)
Lemma eval_stmt_greater: forall s c s' istate istate' istate1,
     eval_stmt s c (SNormal s') -> 
     initializationMap s istate ->
     well_defined_stmt istate c istate' -> 
     initializationMap s' istate1 -> 
     (forall x, (fetch2 x istate' = Some Init -> fetch2 x istate1 = Some Init) /\
                   (fetch2 x istate' = Some Uninit -> exists m, fetch2 x istate1 = Some m)).
Proof.
    intros s c s' istate istate' istate1 h1 h2 h3 h4.
    remember (SNormal s') as s1.
    specialize (eval_stmt_greater_0 _ _ _ _ _ s' istate1 h1 h2 h3); intros hz1.
    destruct hz1.
  - subst. inversion H.
  - apply H; auto.
Qed.

(** 
    according to the lemma eval_stmt_greater, we know that istate' is a subset of istate1, 
    so whenever c2 is well-defined under istate', it should also be well-defined under istate1
*)
Lemma initializationMap_consistent: forall s istate c1 s' istate' c2 istate'' istate1,
     initializationMap s istate ->
     eval_stmt s c1 (SNormal s') -> 
     well_defined_stmt istate c1 istate' -> 
     well_defined_stmt istate' c2 istate'' ->      
     initializationMap s' istate1 ->
     exists istate2, well_defined_stmt istate1 c2 istate2.
Proof.
    intros s istate c1 s' istate' c2 istate'' istate1 h1 h2 h3 h4 h5.
    specialize (eval_stmt_greater _ _ _ _ _ _ h2 h1 h3 h5); intros hz1.
    specialize (initializationMap_stmt _ _ _ _ h4 hz1); intros hz2.
    assumption.
Qed.


(* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -*)
(* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -*)

(** * Correctness Proof About Well-Formed Command *)

(** 
    subset is introduced to prove eval_expr_with_checks_correct and eval_stmt_with_checks_correct, 
    otherwise they cannot be proved directly 
*)
Definition subset (cks1: check_points) (cks2: check_points): Prop := 
    forall id ck, fetch_ck id cks1 = Some ck -> fetch_ck id cks2 = Some ck.

Lemma subset_refl: forall ls,
    subset ls ls.
Proof.
    intros.
    unfold subset; intros.
    assumption.
Qed.

Lemma subset_trans: forall cks0 cks1 cks2,
    subset cks0 cks1 ->
    subset cks1 cks2 ->
    subset cks0 cks2.
Proof.
    intros.
    unfold subset in *.
    intros.
    apply H0. apply H.
    assumption.
Qed.

(** 
    if all ast id numbers in checks list ls is less then n, in other words, n is outside the  
   domain of ls, then when we fetch n from ls, of course it returns None
*)
Lemma fetch_ck_none: forall ls n,
    ast_ids_lt ls n ->
    fetch_ck n ls = None.
Proof.
    intros.
    induction H.
    + simpl. 
       remember (beq_nat n ast_id) as b.
       destruct b.
       * symmetry in Heqb. 
         apply beq_nat_true in Heqb; rewrite Heqb in H0.
         omega.
      * assumption.
    + auto.
Qed.

Lemma lt_not_equal: forall x y,
    x < y ->
    beq_nat x y = false.
Proof.
    induction x;
    intros y h1.
    destruct y. 
    inversion h1.
    auto.
    destruct y; intuition.
    simpl. apply IHx.
    intuition.
Qed.

Lemma beq_nat_comm: forall x y,
    beq_nat x y = beq_nat y x.
Proof.
    induction x; intros y.
  - destruct y; auto.
  - destruct y; auto.
    simpl. 
    apply IHx.
Qed.

(** 
   ast_id_inc_expr enforces that all ast id numbers used in expression e are unique and they are increasing,
   cks1 stores the checks (indexed by ast id numbers) that are generated for expression e on top of cks0, 
   if fetch n from cks0 is None and n is smaller than all ast id numbers in expression e, then fetch n 
   from cks1 should also be None
*)
Lemma check_update_expr: forall cks0 e cks1 max n, 
    check_generator_expr cks0 e cks1 ->
    ast_id_inc_expr e max ->
    fetch_ck n cks0 = None ->
    n < get_ast_id_expr e ->
    fetch_ck n cks1 = None.
Proof.
    intros cks0 e cks1 max n h1.
    revert max n.
    induction h1;
    intros max n0 h2 h3 h4;
    simpl in *;
    specialize (lt_not_equal _ _ h4); intros hz1;
    rewrite hz1;
    auto.
  - inversion h2; subst.
    assert (hz2: n0 < get_ast_id_expr e1); intuition.
    assert (hz3: n0 < get_ast_id_expr e2); intuition.
    specialize (IHh1_1 _ _ H4 h3 hz2).
    specialize (IHh1_2 _ _ H5 IHh1_1 hz3);
    assumption.
  - inversion h2; subst.
    assert (hz2: n0 < get_ast_id_expr e); intuition.
    specialize (IHh1 _ _ H2 h3 hz2).
    assumption.
Qed.

(** it's similar to check_update_expr *)
Lemma check_update_stmt: forall cks0 c cks1 max n, 
    check_generator_stmt cks0 c cks1 ->
    ast_id_inc_stmt c max ->
    fetch_ck n cks0 = None ->
    n < get_ast_id_stmt c ->
    fetch_ck n cks1 = None.
Proof.
    intros cks0 c cks1 max n h1.
    revert max n.
    induction h1;
    intros max n0 h2 h3 h4;
    simpl in *;
    specialize (lt_not_equal _ _ h4); intros hz1;
    rewrite hz1;
    inversion h2; subst;
    auto.
  - assert (hz: n0 < get_ast_id_expr e); intuition.
    specialize (check_update_expr _ _ _ _ _ H H3 h3 hz); intros hz2.
    assumption.
  - assert (hz_1: n0 < get_ast_id_stmt c1); intuition.
    assert (hz_2: n0 < get_ast_id_stmt c2); intuition.
    specialize (IHh1_1 _ _ H2 h3 hz_1).
    specialize (IHh1_2 _ _ H3 IHh1_1 hz_2).
    assumption.
  - assert (hz_1: n0 < get_ast_id_expr b); intuition.
    assert (hz_2: n0 < get_ast_id_stmt c); intuition.
    specialize (check_update_expr _ _ _ _ _ H H3 h3 hz_1); intros hz2.
    specialize (IHh1 _ _ H4 hz2 hz_2); assumption.
  - assert (hz_1: n0 < get_ast_id_expr b); intuition.
    assert (hz_2: n0 < get_ast_id_stmt c); intuition.
    specialize (check_update_expr _ _ _ _ _ H H3 h3 hz_1); intros hz2.
    specialize (IHh1 _ _ H4 hz2 hz_2); assumption.
Qed.

(** 
    if ls0 is a subset of ls1 and x has never appeared in ls1, 
    then, ls0 should be a subset of the ls1 added with new element indexed by x 
*)
Lemma check_update: forall x ls1 ls0 flag,
    fetch_ck x ls1 = None ->
    subset ls0 ls1 ->
    subset ls0 ((x, flag) :: ls1).
Proof.
    intros.
    unfold subset in *; intros.
    unfold fetch_ck.
    remember (beq_nat id x) as b.
    destruct b.
  - specialize (H0 _ _ H1).
    symmetry in Heqb.
    apply beq_nat_true in Heqb; subst.
    rewrite H in H0; inversion H0.
  - fold fetch_ck.
    apply H0.
    assumption.
Qed.

Lemma sub_subset: forall x ls0 flag ls1,
    fetch_ck x ls0 = None ->
    subset ((x, flag) :: ls0) ls1 ->
    subset ls0 ls1.
Proof.
    intros.
    unfold subset in *;
    intros.
    apply H0.
    simpl.
    remember (beq_nat id x) as b.
    destruct b.
  - symmetry in Heqb.
    apply beq_nat_true in Heqb; subst.
    rewrite H in H1; inversion H1.
  - assumption.    
Qed. 


(** 
    cks1 is a list of checks that are generated for expression e on top of cks0, so cks1 
    should be a superset of cks0;
    ast_id_inc_expr enforces that all ast id numbers used in e are unique and increasing,
    and ast_id_lt constrains that all ast ids in cks0 is smaller than the ast ids used in e, 
    this is an implicit requirement enforced by check_generator_expr, for example: 
    for binary expression e1 op e2, [check_generator_expr nil (e1 op e2) cks1] can be computed
    by [check_generator_expr nil e1 cks0]  and [check_generator_expr cks0 e2 cks1], because the 
    ast ids are increasing inside the expression, so all ast ids in cks0 should be smaller than the ast ids in e2;
*)
Lemma subset_expr: forall cks0 e cks1 max,
    check_generator_expr cks0 e cks1 ->
    ast_ids_lt cks0 (get_ast_id_expr e) -> (* make sure that all ast num used in e is fresh *)
    ast_id_inc_expr e max -> (* make sure that all ast numbers are unique and increase *)
    subset cks0 cks1.
Proof.
    intros cks0 e cks1 max h1 h2.
    revert max.
    induction h1; simpl in h2;
    intros max h3.
  - inversion h3; subst.
    unfold subset; intros.
    simpl. 
    remember (beq_nat id max) as b.
    destruct b.
    symmetry in Heqb; apply beq_nat_true in Heqb; subst.
    specialize (fetch_ck_none _ _ h2); intros hz1.
    rewrite hz1 in H0; inversion H0.
    auto.
  - inversion h3; subst.
    unfold subset; intros.
    simpl. 
    remember (beq_nat id max) as b.
    destruct b.
    symmetry in Heqb; apply beq_nat_true in Heqb; subst.
    specialize (fetch_ck_none _ _ h2); intros hz1.
    rewrite hz1 in H0; inversion H0.
    auto.
  - inversion h3; subst.
    specialize (ast_ids_lt_trans _ _ _ h2 H9); intros hz1.
    specialize (ast_ids_lt_trans _ _ _ h2 H10); intros hz2.
    specialize (IHh1_1 hz1 _ H4).
    specialize (ast_id_max_expr _ _ _ _ H4 h1_1 hz1); intros hz3.
    assert (hz: max1 + 1 <= get_ast_id_expr e2); intuition.
    specialize (ast_ids_lt_trans0 _ _ _ hz3 hz); intros hz4.
    specialize (IHh1_2 hz4 _ H5).
    specialize (subset_trans _ _ _ IHh1_1 IHh1_2); intros hz5.

    specialize (fetch_ck_none _ _ h2); intros h1_3.
    specialize (check_update_expr _ _ _ _ _ h1_1 H4 h1_3 H9); intros h1_4.
    specialize (check_update_expr _ _ _ _ _ h1_2 H5 h1_4 H10); intros h1_5.
    specialize (check_update _ _ _ flag h1_5 hz5); intros hz6.
    assumption. 
  - inversion h3; subst.
    specialize (ast_ids_lt_trans _ _ _ h2 H5); intros hz1.
    specialize (IHh1 hz1 _ H2).
    unfold subset; intros.
    simpl. 
    remember (beq_nat id ast_id) as b.
    destruct b.
    symmetry in Heqb; apply beq_nat_true in Heqb; subst.
    specialize (fetch_ck_none _ _ h2); intros hz2.
    rewrite hz2 in H0; inversion H0.
    apply IHh1. assumption.
Qed.


(** it's similar to subset_expr *)
Lemma subset_stmt: forall cks0 c cks1 max,
    check_generator_stmt cks0 c cks1 ->
    ast_ids_lt cks0 (get_ast_id_stmt c) -> 
    ast_id_inc_stmt c max ->
    subset cks0 cks1.
Proof.
    intros cks0 c cks1 max h1.
    revert max.
    induction h1; 
    intros max h2 h3;
    simpl in h2; inversion h3; subst.
  - (* Sassign *)
    specialize (ast_ids_lt_trans _ _ _ h2 H6); intros hz1.
    specialize (subset_expr _ _ _ _ H hz1 H3); intros hz2.
    
    specialize (fetch_ck_none _ _ h2); intros h1_1.
    specialize (check_update_expr _ _ _ _ _ H H3 h1_1 H6); intros h1_2.
    specialize (check_update _ _ _ No_Check h1_2 hz2); intros hz3.
    assumption.
  - (* Sseq *)
    specialize (ast_ids_lt_trans _ _ _ h2 H6); intros hz1.
    specialize (IHh1_1 _ hz1 H2).
    specialize (ast_id_max_stmt _ _ _ _ H2 h1_1 hz1); intros hz2.
    assert (hz: max1 + 1 <= get_ast_id_stmt c2); intuition.
    specialize (ast_ids_lt_trans0 _ _ _ hz2 hz); intros hz3.
    specialize (IHh1_2 _ hz3 H3).
    specialize (subset_trans _ _ _ IHh1_1 IHh1_2); intros hz4.
    
    specialize (fetch_ck_none _ _ h2); intros h1_3.
    specialize (check_update_stmt _ _ _ _ _ h1_1 H2 h1_3 H6); intros h1_4.
    specialize (check_update_stmt _ _ _ _ _ h1_2 H3 h1_4 H8); intros h1_5.
    specialize (check_update _ _ _ No_Check h1_5 hz4); intros hz5.
    assumption.
  - (* Sifthen *)
    specialize (ast_ids_lt_trans _ _ _ h2 H7); intros hz1.
    specialize (ast_id_max_expr _ _ _ _ H3 H hz1); intros hz2.
    assert (hz: max1 + 1 <= get_ast_id_stmt c); intuition.
    specialize (ast_ids_lt_trans0 _ _ _ hz2 hz); intros hz3.
    specialize (IHh1 _ hz3 H4).
    specialize (subset_expr _ _ _ _ H hz1 H3); intros hz4.
    specialize (subset_trans _ _ _ hz4 IHh1); intros hz5.
    
    specialize (fetch_ck_none _ _ h2); intros h1_3.
    specialize (check_update_expr _ _ _ _ _ H H3 h1_3 H7); intros h1_4.
    specialize (check_update_stmt _ _ _ _ _ h1 H4 h1_4 H9); intros h1_5.
    specialize (check_update _ _ _ No_Check h1_5 hz5); intros hz6.
    assumption.    
  - (* Swhile *)
    specialize (ast_ids_lt_trans _ _ _ h2 H7); intros hz1.
    specialize (ast_id_max_expr _ _ _ _ H3 H hz1); intros hz2.
    assert (hz: max1 + 1 <= get_ast_id_stmt c); intuition.
    specialize (ast_ids_lt_trans0 _ _ _ hz2 hz); intros hz3.
    specialize (IHh1 _ hz3 H4).
    specialize (subset_expr _ _ _ _ H hz1 H3); intros hz4.
    specialize (subset_trans _ _ _ hz4 IHh1); intros hz5.

    specialize (fetch_ck_none _ _ h2); intros h1_3.
    specialize (check_update_expr _ _ _ _ _ H H3 h1_3 H7); intros h1_4.
    specialize (check_update_stmt _ _ _ _ _ h1 H4 h1_4 H9); intros h1_5.
    specialize (check_update _ _ _ No_Check h1_5 hz5); intros hz6.
    assumption.     
Qed.

(** 
    cks1 is a list of checks that are generated for expression e on top of cks0, 
    if max is the maximum ast id number used inside e and all ast ids in cks0 are less than ast ids used in e,
    then for any n greater than max, n should be greater than all ast ids stored in cks1
*)
Lemma lt_trans_expr: forall cks0 cks1 e max n,
    check_generator_expr cks0 e cks1 ->
    ast_ids_lt cks0 (get_ast_id_expr e) ->
    ast_id_inc_expr e max ->
    max < n ->
    ast_ids_lt cks1 n.
Proof.
    intros.
    specialize (ast_id_max_expr _ _ _ _ H1 H H0); intros h1.
    assert (h2: max + 1 <= n); intuition.
    specialize (ast_ids_lt_trans0 _ _ _ h1 h2); intros h3.
    assumption.
Qed.

(* it's similar to lt_trans_expr *)
Lemma lt_trans_stmt: forall cks0 cks1 c max n,
    check_generator_stmt cks0 c cks1 ->
    ast_ids_lt cks0 (get_ast_id_stmt c) ->
    ast_id_inc_stmt c max ->
    max < n ->
    ast_ids_lt cks1 n.
Proof.
    intros.
    specialize (ast_id_max_stmt _ _ _ _ H1 H H0); intros h1.
    assert (h2: max + 1 <= n); intuition.
    specialize (ast_ids_lt_trans0 _ _ _ h1 h2); intros h3.
    assumption.
Qed.


(** 
    help1 and help2 are just help lemmas that are used repeatedly to prove eval_expr_with_checks_correct0, 
    so I define them as lemmas
*)
Lemma help1: forall ls0 ls1 ls2 ast_id e1 e2 max1 max2,
    ast_ids_lt ls0 ast_id ->
    ast_id < get_ast_id_expr e1 -> 
    max1 < get_ast_id_expr e2 -> 
    check_generator_expr ls0 e1 ls1 ->
    check_generator_expr ls1 e2 ls2 -> 
    ast_id_inc_expr e1 max1 ->
    ast_id_inc_expr e2 max2 -> 
    subset ls1 ls2.
Proof.
    intros.
    specialize (ast_ids_lt_trans _ _ _ H H0); intros hz1.
    specialize (lt_trans_expr _ _ _ _ _ H2 hz1 H4 H1); intros hz2.
    specialize (subset_expr _ _ _ _ H3 hz2 H5); intros hz5.
    assumption.
Qed.


Lemma help2: forall cks0 ls1 ls2 cks ast_id e1 e2 max1 max2 flag, 
    ast_ids_lt cks0 ast_id ->
    check_generator_expr cks0 e1 ls1 ->
    check_generator_expr ls1 e2 ls2 ->
    ast_id_inc_expr e1 max1 ->
    ast_id_inc_expr e2 max2 -> 
    ast_id < get_ast_id_expr e1 ->
    ast_id < get_ast_id_expr e2 ->
    subset ((ast_id, flag) :: ls2) cks ->
    subset ls2 cks.
Proof.
    intros.
    specialize (fetch_ck_none _ _ H); intros h1.
    specialize (check_update_expr _ _ _ _ _ H0 H2 h1 H4); intros h2.
    specialize (check_update_expr _ _ _ _ _ H1 H3 h2 H5); intros h3.
    specialize (sub_subset _ _ _ _ h3 H6); intros hz4.
    assumption.
Qed.

(** 
    Because we cannot prove eval_expr_with_checks_correct directly, so 
    eval_expr_with_checks_correct0 is proved as an intermediate proof step by introducing "subset";
    it means that if cks1 is checks that are generated for expression e on top of cks0, and cks is a 
    superset of cks1, then whenever e is evaluated to value v under checks cks, expression
    e can also evaluate to value v in relational semantics eval_expr;
    all ast nodes in expression e are denoted with either checks or no checks by cks1, so even if cks is 
    a superset of cks1, all these extra checks in cks cannot affect the evaluation of expression e
*)
Lemma eval_expr_with_checks_correct0: forall cks s e v cks1 cks0 max,
    eval_expr_with_checks cks s e v ->
    subset cks1 cks ->
    check_generator_expr cks0 e cks1 ->
    ast_ids_lt cks0 (get_ast_id_expr e) ->
    ast_id_inc_expr e max ->
    eval_expr s e v.
Proof.
    intros cks s e v cks1 cks0 max h1.
    generalize cks1 cks0 max.
    clear cks1 cks0 max.
    induction h1;
    intros cks1 cks0 max h2 h3 h4 h5;
    simpl in h4;
    inversion h3; subst;
    inversion h5; subst.
  - (* Econst *) 
    constructor; auto.
  - (* Evar *)
    constructor; auto.
  - (* Ebinop *)
    specialize (ast_ids_lt_trans _ _ _ h4 H11); intros hz1.    
    specialize (help1 _ _ _ _ _ _ _ _ h4 H11 H13 H5 H6 H3 H4); intros hz_1.
    specialize (help2 _ _ _ _ _ _ _ _ _ _ h4 H5 H6 H3 H4 H11 H12 h2); intros hz_2.
    specialize (subset_trans _ _ _ hz_1 hz_2); intros hz2.
    specialize (IHh1 _ _ _ hz2 H5 hz1 H3).
    apply eval_Ebinop1; assumption.
  - specialize (ast_ids_lt_trans _ _ _ h4 H11); intros hz1.
    specialize (help1 _ _ _ _ _ _ _ _ h4 H11 H13 H5 H6 H3 H4); intros hz_1.    
    specialize (help2 _ _ _ _ _ _ _ _ _ _ h4 H5 H6 H3 H4 H11 H12 h2); intros hz_2.
    specialize (subset_trans _ _ _ hz_1 hz_2); intros hz2.
    specialize (IHh1_1 _ _ _ hz2 H5 hz1 H3).
    
    specialize (lt_trans_expr _ _ _ _ _ H5 hz1 H3 H13); intros hz3.
    specialize (IHh1_2 _ _ _ hz_2 H6 hz3 H4).
    eapply eval_Ebinop2. 
    apply IHh1_1.
    assumption.
  - specialize (ast_ids_lt_trans _ _ _ h4 H13); intros hz1.
    specialize (help1 _ _ _ _ _ _ _ _ h4 H13 H15 H7 H8 H5 H6); intros hz_1.    
    specialize (help2 _ _ _ _ _ _ _ _ _ _ h4 H7 H8 H5 H6 H13 H14 h2); intros hz_2.
    specialize (subset_trans _ _ _ hz_1 hz_2); intros hz2.
    specialize (IHh1_1 _ _ _ hz2 H7 hz1 H5).
    
    specialize (lt_trans_expr _ _ _ _ _ H7 hz1 H5 H15); intros hz_3.
    specialize (IHh1_2 _ _ _ hz_2 H8 hz_3 H6).
    eapply eval_Ebinop3. apply IHh1_1. apply IHh1_2.
    inversion H9; subst.
    { unfold subset in h2. specialize (h2 ast_id (Division_Check (Ebinop ast_id Odiv e1 e2))).
      simpl in h2; rewrite <- beq_nat_refl in h2; intuition.
      rewrite H in H1; inversion H1; subst.
      econstructor. constructor. 
      inversion H0; subst.
      specialize (eval_expr_with_checks_unique _ _ _ _ _ h1_1 H11); intros hz3.
      specialize (eval_expr_with_checks_unique _ _ _ _ _ h1_2 H16); intros hz4.
      subst.
      econstructor.
      apply IHh1_1. apply IHh1_2.
      assumption.
    }
    { unfold subset in h2. specialize (h2 ast_id No_Check).
      simpl in h2; rewrite <- beq_nat_refl in h2; intuition.
      rewrite H in H1; inversion H1; subst.
      inversion H0.
    }
  - specialize (ast_ids_lt_trans _ _ _ h4 H14); intros hz1.
    specialize (help1 _ _ _ _ _ _ _ _ h4 H14 H16 H9 H10 H6 H7); intros hz_1.    
    specialize (help2 _ _ _ _ _ _ _ _ _ _ h4 H9 H10 H6 H7 H14 H15 h2); intros hz_2.
    specialize (subset_trans _ _ _ hz_1 hz_2); intros hz2.
    specialize (IHh1_1 _ _ _ hz2 H9 hz1 H6).
    
    specialize (lt_trans_expr _ _ _ _ _ H9 hz1 H6 H16); intros hz_3.
    specialize (IHh1_2 _ _ _ hz_2 H10 hz_3 H7).
    eapply eval_Ebinop4; auto; try assumption.
    inversion H11; subst.
    { unfold subset in h2. specialize (h2 ast_id (Division_Check (Ebinop ast_id Odiv e1 e2))).
      simpl in h2; rewrite <- beq_nat_refl in h2; intuition.
      rewrite H in H1; inversion H1; subst.
      econstructor. constructor. 
      inversion H0; subst. 
      specialize (eval_expr_with_checks_unique _ _ _ _ _ h1_1 H12); intros hz3.
      specialize (eval_expr_with_checks_unique _ _ _ _ _ h1_2 H17); intros hz4.
      subst.
      econstructor.
      apply IHh1_1. apply IHh1_2.
      assumption.
    }
    { econstructor. constructor.
      assumption.
      constructor.
    }
  - (* Eunop *)
    specialize (ast_ids_lt_trans _ _ _ h4 H6); intros hz1.
    specialize (fetch_ck_none _ _ h4); intros h_1.
    specialize (check_update_expr _ _ _ _ _ H2 H1 h_1 H6); intros h_2.
    specialize (sub_subset _ _ _ _ h_2 h2); intros hz2.
    specialize (IHh1 _ _ _ hz2 H2 hz1 H1).
    econstructor; assumption.
  - specialize (ast_ids_lt_trans _ _ _ h4 H7); intros hz1.
    specialize (fetch_ck_none _ _ h4); intros h_1.
    specialize (check_update_expr _ _ _ _ _ H4 H2 h_1 H7); intros h_2.
    specialize (sub_subset _ _ _ _ h_2 h2); intros hz2.
    specialize (IHh1 _ _ _ hz2 H4 hz1 H2).
    
    econstructor; auto.
    assumption.
Qed.

(**
    cks is checks that are generated for expression e according to the checking rules built on top of cks0, 
    then whenever e is evaluated to value v under checks cks, expression e can also be evaluated to value v 
    in relational semantics eval_expr;
    ast_id_inc_expr is used to constrain that all ast ids used in e are unique and increasing;
    ast_ids_lt is used to enforce that new checks added for expression e will not cover the checks cks0 built
    for previous AST nodes
*)
Theorem eval_expr_with_checks_correct: forall cks s e v cks0 max,
    eval_expr_with_checks cks s e v ->
    check_generator_expr cks0 e cks ->
    ast_ids_lt cks0 (get_ast_id_expr e) ->
    ast_id_inc_expr e max ->
    eval_expr s e v.
Proof.
    intros.
    specialize (subset_refl cks); intros hz1.
    specialize (eval_expr_with_checks_correct0 _ _ _ _ _ _ _ H hz1 H0 H1 H2).
    auto.
Qed.

(*
(* The Proof in other way *)
Theorem eval_expr_with_checks_correct: forall cks0 e cks max s v,
    check_generator_expr cks0 e cks ->
    ast_ids_lt cks0 (get_ast_id_expr e) ->
    ast_id_inc_expr e max ->
    eval_expr_with_checks cks s e v ->
    eval_expr s e v.
Proof.
    intros cks0 e cks max s v h1.
    generalize max s v.
    induction h1;
    intros max0 s0 v0 h2 h3 h4.
  - (* Econst *)
    inversion h4; subst.
    constructor; auto.
  - (* Evar *)
    inversion h4; subst.    
    constructor; auto.
  - (* Ebinop *)
    simpl in h2.
    inversion h3; subst.
    inversion h4; subst.
    + specialize (ast_ids_lt_trans _ _ _ h2 H9); intros hz1.
       specialize (eval_expr_infer1 _ _ _ _ _ _ H9 H8); intros hz2.
       specialize (eval_expr_infer _ _ _ _ _ _ _ hz1 h1_1 h1_2 hz2); intros hz3.
       specialize (IHh1_1 _ _ _ hz1 H4 hz3).
       apply eval_Ebinop1. 
       assumption.
    + specialize (ast_ids_lt_trans _ _ _ h2 H9); intros hz1;
       specialize (eval_expr_infer1 _ _ _ _ _ _ H9 H8); intros hz2;
       specialize (eval_expr_infer _ _ _ _ _ _ _ hz1 h1_1 h1_2 hz2); intros hz3;
       specialize (IHh1_1 _ _ _ hz1 H4 hz3).
       specialize (ast_id_inc _ _ _ _ hz1 h1_1 H4); intros hz2_1;
       assert(hz2_2: max1 + 1 <= get_ast_id_expr e2); intuition;
       specialize (ast_ids_lt_trans0 _ _ _ hz2_1 hz2_2); intros hz2_3;
       specialize (eval_expr_infer1 _ _ _ _ _ _ H10 H12); intros hz5;
       specialize (IHh1_2 _ _ _ hz2_3 H5 hz5).
       eapply eval_Ebinop2; try assumption.
       apply IHh1_1.
    + specialize (ast_ids_lt_trans _ _ _ h2 H9); intros hz1;
       specialize (eval_expr_infer1 _ _ _ _ _ _ H9 H7); intros hz2;
       specialize (eval_expr_infer _ _ _ _ _ _ _ hz1 h1_1 h1_2 hz2); intros hz3;
       specialize (IHh1_1 _ _ _ hz1 H4 hz3).
       specialize (ast_id_inc _ _ _ _ hz1 h1_1 H4); intros hz2_1;
       assert(hz2_2: max1 + 1 <= get_ast_id_expr e2); intuition;
       specialize (ast_ids_lt_trans0 _ _ _ hz2_1 hz2_2); intros hz2_3;
       specialize (eval_expr_infer1 _ _ _ _ _ _ H10 H12); intros hz5;
       specialize (IHh1_2 _ _ _ hz2_3 H5 hz5).
       eapply eval_Ebinop3.
       apply IHh1_1. apply IHh1_2.
       inversion H; subst;
       simpl in H13; rewrite <- beq_nat_refl in H13; inversion H13; subst.
       { 
         econstructor. constructor. 
         inversion H14; subst.
         specialize (eval_expr_with_checks_unique _ _ _ _ _ H7 H6); intros hz4.
         specialize (eval_expr_with_checks_unique _ _ _ _ _ H12 H15); intros hz6.
         subst.
         econstructor.
         apply IHh1_1. apply IHh1_2.
         assumption.
       }
       { 
         inversion H14.
       }
    + specialize (ast_ids_lt_trans _ _ _ h2 H9); intros hz1.
       specialize (eval_expr_infer1 _ _ _ _ _ _ H9 H6); intros hz2;
       specialize (eval_expr_infer _ _ _ _ _ _ _ hz1 h1_1 h1_2 hz2); intros hz3;
       specialize (IHh1_1 _ _ _ hz1 H4 hz3).
       specialize (ast_id_inc _ _ _ _ hz1 h1_1 H4); intros hz2_1;
       assert(hz2_2: max1 + 1 <= get_ast_id_expr e2); intuition;
       specialize (ast_ids_lt_trans0 _ _ _ hz2_1 hz2_2); intros hz2_3;
       specialize (eval_expr_infer1 _ _ _ _ _ _ H10 H7); intros hz5;
       specialize (IHh1_2 _ _ _ hz2_3 H5 hz5).
       econstructor.
       * apply IHh1_1.
       * apply IHh1_2.
       * destruct op;
         inversion H; subst;
         match goal with
         | [h: check_flag (Ebinop ?ast_id Odiv ?e1 ?e2) ?check |- run_time_check eval_expr ?s0 (Ebinop ?ast_id Odiv ?e1 ?e2) true ] => idtac
         | [h: check_flag (Ebinop ?ast_id ?op ?e1 ?e2) ?check |- run_time_check eval_expr ?s0 (Ebinop ?ast_id ?op ?e1 ?e2) true ] => 
               econstructor; [apply H | constructor]
         end. 
         { simpl in H12. rewrite <- beq_nat_refl in H12. inversion H12; subst.
           econstructor. constructor. 
           destruct v1; destruct v2;
           unfold eval_binop in H16; simpl in H16; intuition.
           econstructor. apply IHh1_1. apply IHh1_2.         
           inversion H14; subst.
           specialize (eval_expr_with_checks_unique _ _ _ _ _ H7 H15); intros hz4.
           inversion hz4; subst; assumption.
         }
         { simpl in H12. rewrite <- beq_nat_refl in H12. inversion H12; subst.
           intuition.
         }
      * reflexivity.
      * destruct v1; destruct v2;
        destruct op;
        match goal with
        [h: eval_binop ?op ?v1 ?v2 = ValAbnormal -> False |- _ ] => simpl in h; intuition
        end.
  - (* Eunop *)
    simpl in h2.
    inversion h3; subst.
    inversion h4; subst.
    + specialize (eval_expr_infer1 _ _ _ _ _ _ H5 H6); intros hz1.
       specialize (ast_ids_lt_trans _ _ _ h2 H5); intros hz2.
       specialize (IHh1 _ _ _ hz2 H2 hz1).
       econstructor. 
       assumption.
    + specialize (eval_expr_infer1 _ _ _ _ _ _ H5 H3); intros hz1.
       specialize (ast_ids_lt_trans _ _ _ h2 H5); intros hz2.
       specialize (IHh1 _ _ _ hz2 H2 hz1).
       econstructor; auto. 
       apply IHh1. 
       destruct op, op0; reflexivity.
Qed.
*)

(** these help lemmas are used to finally prove eval_stmt_with_checks_correct *)
Lemma help3: forall cks0 cks1 cks2 c1 c2 max1 max2,
    check_generator_stmt cks0 c1 cks1 ->
    check_generator_stmt cks1 c2 cks2 ->
    ast_id_inc_stmt c1 max1 ->
    ast_id_inc_stmt c2 max2 ->
    ast_ids_lt cks0 (get_ast_id_stmt c1) ->
    max1 < get_ast_id_stmt c2 ->
    subset cks1 cks2.
Proof.
    intros.
    specialize (lt_trans_stmt _ _ _ _ _ H H3 H1 H4); intros hz1.
    specialize (subset_stmt _ _ _ _ H0 hz1 H2); intuition.
Qed.

Lemma help4: forall cks0 cks1 cks2 cks3 c1 c2 max1 max2 ast_id flag,
    check_generator_stmt cks0 c1 cks1 ->
    check_generator_stmt cks1 c2 cks2 -> 
    ast_id_inc_stmt c1 max1 ->
    ast_id_inc_stmt c2 max2 ->
    ast_id < get_ast_id_stmt c1 ->
    ast_id < get_ast_id_stmt c2 ->
    ast_ids_lt cks0 ast_id ->
    subset ((ast_id, flag) :: cks2) cks3 ->
    subset cks2 cks3.
Proof.
    intros.
    specialize (fetch_ck_none _ _ H5); intros hz1.
    specialize (check_update_stmt _ _ _ _ _ H H1 hz1 H3); intros hz2.
    specialize (check_update_stmt _ _ _ _ _ H0 H2 hz2 H4); intros hz3.
    specialize (sub_subset _ _ _ _ hz3 H6); intros hz4.
    assumption.
Qed.


Lemma help5: forall cks0 cks1 cks2 b c max1 max2 ast_id,
    check_generator_expr cks0 b cks1 ->
    check_generator_stmt cks1 c cks2 ->
    ast_id_inc_expr b max1 ->
    ast_id_inc_stmt c max2 ->
    max1 < get_ast_id_stmt c ->
    ast_id < get_ast_id_expr b ->
    ast_ids_lt cks0 ast_id ->
    subset cks1 cks2.
Proof.
    intros.
    specialize (ast_ids_lt_trans _ _ _ H5 H4); intros hz1.
    specialize (lt_trans_expr _ _ _ _ _ H hz1 H1 H3); intros hz2.
    specialize (subset_stmt _ _ _ _ H0 hz2 H2); intros hz5.
    assumption.
Qed.

Lemma help6: forall cks0 cks1 cks2 cks3 b c max1 max2 ast_id flag,
    check_generator_expr cks0 b cks1 ->
    check_generator_stmt cks1 c cks2 ->
    ast_id_inc_expr b max1 ->
    ast_id_inc_stmt c max2 ->
    ast_id < get_ast_id_expr b ->
    ast_id < get_ast_id_stmt c -> 
    ast_ids_lt cks0 ast_id ->
    subset ((ast_id, flag) :: cks2) cks3 ->
    subset cks2 cks3.
Proof.
    intros.
    specialize (fetch_ck_none _ _ H5); intros hz_1.
    specialize (check_update_expr _ _ _ _ _ H H1 hz_1 H3); intros hz_2.
    specialize (check_update_stmt _ _ _ _ _ H0 H2 hz_2 H4); intros hz_3.
    specialize (sub_subset _ _ _ _ hz_3 H6); intros hz_4.
    assumption.
Qed.

(** 
    Because we cannot prove eval_stmt_with_checks_correct directly, so 
    eval_stmt_with_checks_correct0 is proved as an intermediate proof step by introducing "subset",
    it's similar to eval_expr_with_checks_correct0
*)
Theorem eval_stmt_with_checks_correct_0: forall cks s c s' cks1 cks0 max,
    eval_stmt_with_checks cks s c s' ->
    subset cks1 cks ->
    check_generator_stmt cks0 c cks1 ->
    ast_ids_lt cks0 (get_ast_id_stmt c) ->
    ast_id_inc_stmt c max ->
    eval_stmt s c s'.
Proof.
    intros cks s c s' cks1 cks0 max h1.
    generalize cks1 cks0 max.
    clear cks1 cks0 max.
    induction h1;
    intros cks1 cks0 max h2 h3 h4 h5;
    simpl in h4; inversion h3; inversion h5; subst.
  - (* Sassign *)
    specialize (ast_ids_lt_trans _ _ _ h4 H12); intros hz1.
    specialize (fetch_ck_none _ _ h4); intros h_1.
    specialize (check_update_expr _ _ _ _ _ H5 H9 h_1 H12); intros h_2.
    specialize (sub_subset _ _ _ _ h_2 h2); intros hz2.
    specialize (eval_expr_with_checks_correct0 _ _ _ _ _ _ _ H hz2 H5 hz1 H9); intros hz3.
    constructor;
    assumption.
  - specialize (ast_ids_lt_trans _ _ _ h4 H13); intros hz1.
    specialize (fetch_ck_none _ _ h4); intros h_1.
    specialize (check_update_expr _ _ _ _ _ H6 H10 h_1 H13); intros h_2.
    specialize (sub_subset _ _ _ _ h_2 h2); intros hz2.
    specialize (eval_expr_with_checks_correct0 _ _ _ _ _ _ _ H hz2 H6 hz1 H10); intros hz3.
    econstructor.
    apply hz3.
    assumption.
  - (* Sseq *)
    specialize (ast_ids_lt_trans _ _ _ h4 H13); intros hz1.
    specialize (help3 _ _ _ _ _ _ _ H4 H5 H9 H10 hz1 H16); intros hz_1.
    specialize (help4 _ _ _ _ _ _ _ _ _ _ H4 H5 H9 H10 H13 H15 h4 h2); intros hz_2.
    specialize (subset_trans _ _ _ hz_1 hz_2); intros hz2.
    specialize (IHh1 _ _ _ hz2 H4 hz1 H9).
    constructor; assumption.
  - specialize (ast_ids_lt_trans _ _ _ h4 H13); intros hz1.
    specialize (help3 _ _ _ _ _ _ _ H4 H5 H9 H10 hz1 H16); intros hz_1.
    specialize (help4 _ _ _ _ _ _ _ _ _ _ H4 H5 H9 H10 H13 H15 h4 h2); intros hz_2.
    specialize (subset_trans _ _ _ hz_1 hz_2); intros hz2.
    specialize (IHh1_1 _ _ _ hz2 H4 hz1 H9).

    specialize (lt_trans_stmt _ _ _ _ _ H4 hz1 H9 H16); intros hz3.
    specialize (IHh1_2 _ _ _ hz_2 H5 hz3 H10).
    econstructor.
    apply IHh1_1.
    assumption.
  - (* Sifthen *)
    specialize (ast_ids_lt_trans _ _ _ h4 H14); intros hz1.
    specialize (help5 _ _ _ _ _ _ _ _ H5 H6 H10 H11 H17 H14 h4); intros hz_1.
    specialize (help6 _ _ _ _ _ _ _ _ _ _ H5 H6 H10 H11 H14 H16 h4 h2); intros hz_2.
    specialize (subset_trans _ _ _ hz_1 hz_2); intros hz2.
    specialize (eval_expr_with_checks_correct0 _ _ _ _ _ _ _ H hz2 H5 hz1 H10); intros hz3.
    constructor; 
    assumption.
  - specialize (ast_ids_lt_trans _ _ _ h4 H14); intros hz1.
    specialize (help6 _ _ _ _ _ _ _ _ _ _ H5 H6 H10 H11 H14 H16 h4 h2); intros hz2.
    specialize (lt_trans_expr _ _ _ _ _ H5 hz1 H10 H17); intros hz3.
    specialize (IHh1 _ _ _ hz2 H6 hz3 H11).
    econstructor; try assumption.
    
    specialize (help5 _ _ _ _ _ _ _ _ H5 H6 H10 H11 H17 H14 h4); intros hz4.
    specialize (subset_trans _ _ _ hz4 hz2); intros hz5.
    specialize (eval_expr_with_checks_correct0 _ _ _ _ _ _ _ H hz5 H5 hz1 H10); intros hz6.
    assumption. 
  - apply eval_Sifthen_False.
    specialize (ast_ids_lt_trans _ _ _ h4 H14); intros hz1.
    specialize (help5 _ _ _ _ _ _ _ _ H5 H6 H10 H11 H17 H14 h4); intros hz_1.
    specialize (help6 _ _ _ _ _ _ _ _ _ _ H5 H6 H10 H11 H14 H16 h4 h2); intros hz_2.
    specialize (subset_trans _ _ _ hz_1 hz_2); intros hz2.
    specialize (eval_expr_with_checks_correct0 _ _ _ _ _ _ _ H hz2 H5 hz1 H10); intros hz3.
    assumption.
  - (* Swhile *)
    specialize (ast_ids_lt_trans _ _ _ h4 H14); intros hz1.
    specialize (help5 _ _ _ _ _ _ _ _ H5 H6 H10 H11 H17 H14 h4); intros hz_1.
    specialize (help6 _ _ _ _ _ _ _ _ _ _ H5 H6 H10 H11 H14 H16 h4 h2); intros hz_2.
    specialize (subset_trans _ _ _ hz_1 hz_2); intros hz2.
    specialize (eval_expr_with_checks_correct0 _ _ _ _ _ _ _ H hz2 H5 hz1 H10); intros hz3.
    constructor; 
    assumption.    
  - specialize (ast_ids_lt_trans _ _ _ h4 H14); intros hz1.
    specialize (help6 _ _ _ _ _ _ _ _ _ _ H5 H6 H10 H11 H14 H16 h4 h2); intros hz2.
    specialize (lt_trans_expr _ _ _ _ _ H5 hz1 H10 H17); intros hz3.
    specialize (IHh1 _ _ _ hz2 H6 hz3 H11). 
    apply eval_Swhile_True1; try assumption.
    specialize (help5 _ _ _ _ _ _ _ _ H5 H6 H10 H11 H17 H14 h4); intros hz4.
    specialize (subset_trans _ _ _ hz4 hz2); intros hz5.
    specialize (eval_expr_with_checks_correct0 _ _ _ _ _ _ _ H hz5 H5 hz1 H10); intros hz6.
    assumption.
  - specialize (ast_ids_lt_trans _ _ _ h4 H14); intros hz1.
    specialize (lt_trans_expr _ _ _ _ _ H5 hz1 H10 H17); intros hz2.
    specialize (help6 _ _ _ _ _ _ _ _ _ _ H5 H6 H10 H11 H14 H16 h4 h2); intros hz3.
    specialize (IHh1_1 _ _ _ hz3 H6 hz2 H11).
    specialize (IHh1_2 _ _ _ h2 h3 h4 h5).
    eapply eval_Swhile_True2.
    specialize (help5 _ _ _ _ _ _ _ _ H5 H6 H10 H11 H17 H14 h4); intros hz4.
    specialize (subset_trans _ _ _ hz4 hz3); intros hz5.
    specialize (eval_expr_with_checks_correct0 _ _ _ _ _ _ _ H hz5 H5 hz1 H10); intros hz6.
    assumption.
    apply IHh1_1.
    assumption.
  - apply eval_Swhile_False.
    specialize (ast_ids_lt_trans _ _ _ h4 H14); intros hz1.
    specialize (help5 _ _ _ _ _ _ _ _ H5 H6 H10 H11 H17 H14 h4); intros hz_1.
    specialize (help6 _ _ _ _ _ _ _ _ _ _ H5 H6 H10 H11 H14 H16 h4 h2); intros hz_2.    
    specialize (subset_trans _ _ _ hz_1 hz_2); intros hz2.
    specialize (eval_expr_with_checks_correct0 _ _ _ _ _ _ _ H hz2 H5 hz1 H10); intros hz3.
    assumption.
Qed.

(**
    cks is checks that are generated for statement c according to the checking rules built on top of cks0, 
    then whenever c is evaluated to a state s' under checks cks, statement c can also be evaluated to state s' 
    in relational semantics eval_stmt;
    ast_id_inc_stmt is used to constrain that all ast ids used in c are unique and increasing;
    ast_ids_lt is used to enforce that new checks added for c will not cover the checks cks0 built
    for previous AST nodes
*)
Theorem eval_stmt_with_checks_correct: forall cks s c s' cks0 max,
    eval_stmt_with_checks cks s c s' ->
    check_generator_stmt cks0 c cks ->
    ast_ids_lt cks0 (get_ast_id_stmt c) ->
    ast_id_inc_stmt c max ->
    eval_stmt s c s'.
Proof.
    intros.
    specialize (subset_refl cks); intros hz1.
    specialize (eval_stmt_with_checks_correct_0 _ _ _ _ _ _ _ H hz1 H0 H1 H2).
    auto.
Qed.

