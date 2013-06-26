Require Export util.
Require Export wellformed.

(** * Properties Proof *)

Ltac rm_contradict := 
    match goal with
    | [h: return_value_type ValException Tint |- _ ] =>  inversion h
    | [h: return_value_type ValException Tbool |- _ ] =>  inversion h
    | [h: return_value_type (ValNormal (Bool _)) Tint |- _ ] =>  inversion h
    | [h: return_value_type (ValNormal (Int _)) Tbool |- _ ] =>  inversion h
    | [h: Some ?T = binop_type ?OP Tint Tbool |- _ ] => unfold binop_type in h; simpl in h; inversion h
    | [h: Some ?T = binop_type ?OP Tbool Tint |- _ ] => unfold binop_type in h; simpl in h; inversion h
    end.

Ltac rm_contradict2 :=
    match goal with
    | [h: return_value_type ValException ?t |- _] => destruct t; inversion h
    end.

(** the type of the expression evaluation result should be consistent with the type  
     computed by the type checker
*)
Lemma eval_type_reserve: forall tb s e v t,
    type_check_stack tb s -> 
    eval_expr s e v ->
    well_typed_expr tb e t ->
    return_value_type v t.
Proof.
    intros s tb e.
    induction e;
    intros v t h1 h2 h3;
    inversion h3;
    inversion h2; subst.
  - (* Econst *)
    constructor.
  - constructor.  
  - (* Evar *)
    specialize (typed_value _ _ i v0 h1 ); intros hz1.
    specialize (hz1 H8).
    rm_exists.
    rewrite H3 in H. inversion H; subst.
    apply value_type_consistent; assumption.
  - (* Ebinop *)
    specialize (IHe1 _ _ h1 H14 H5).
    specialize (IHe2 _ _ h1 H15 H6).
    destruct v1 as [v11 | v12]; try rm_contradict2.
    destruct v2 as [v21 | v22]; try rm_contradict2.
    destruct v11; destruct v21;
    destruct t0; try rm_contradict.
    + destruct b; repeat simpl_binop_hyp;
       try constructor.
    + destruct b; try simpl_binop_hyp;
       constructor.
  - (* Eunop *)
    unfold eval_unop; destruct op; simpl.
    constructor.
(* another possible proof:
    - - - - - - - - - - - - - - - - 
    intros s tb e v t h1 h2.
    generalize t.
    induction h2; subst; 
    intros t0 h3.
  - (* Econst *)
    inversion h3; subst;
    constructor.
  - (* Evar *)
    inversion h3; subst.
    inversion h1; subst.
    specialize (H0 _ _ H).
    rm_exists.
    rewrite H2 in H4. 
    inversion H4; subst.
    apply value_type_consistent; assumption.
  - (* Ebinop *)
    inversion h3; subst.
    specialize (IHh2_1 h1 _ H6).
    specialize (IHh2_2 h1 _ H7).
    destruct v1 as [v11 | v12]; try rm_contradict2.
    destruct v2 as [v21 | v22]; try rm_contradict2.
    destruct v11 as [v1i | v1b];
    destruct v21 as [v2i | v2b];
    inversion IHh2_1; subst.
    ...
*)
Qed.

Lemma exceptionVal_has_no_typ: forall tb s e t, 
    type_check_stack tb s ->
    eval_expr s e ValException -> 
    well_typed_expr tb e t ->
    False.
Proof.
    intros s tb e t h1 h2 h3.
    specialize (eval_type_reserve _ _ _ _ _ h1 h2 h3).
    intros h4.
    destruct t; inversion h4.
Qed.


(* basic lemmas *)
Ltac br_rm_rop v1 v2 op v1' v2' :=
    match goal with
    | [ |- exists v : value, eval_expr _ (Ebinop ?ast_id ?rop ?e1 ?e2) (ValNormal ?v)] =>
            assert (exists b, eval_binop rop (ValNormal v1) (ValNormal v2) = ValNormal (Bool b))
    end; [ simpl_binop; exists (op v1' v2'); auto | ].

Ltac br_rm_aop v1 v2 v3 :=
    match goal with
    | [ |- exists v : value, eval_expr _ (Ebinop ?ast_id ?aop ?e1 ?e2) (ValNormal ?v)] =>
            assert (exists n, eval_binop aop (ValNormal v1) (ValNormal v2) = ValNormal (Int n))
    end; [ simpl_binop; exists v3; auto | ].

Ltac br_clearer v f :=
    exists v;
    rm_eval_expr; unfold f; auto.   

Lemma binop_rule: forall tb s e1 v1 e2 v2 ast_id op t,
    type_check_stack tb s -> 
    eval_expr s e1 (ValNormal v1) ->
    eval_expr s e2 (ValNormal v2) -> 
    well_typed_expr tb (Ebinop ast_id op e1 e2) t -> (* for example, disallow expression: 8 /\ 9 *)
    (exists v : value, eval_expr s (Ebinop ast_id op e1 e2) (ValNormal v)).
Proof.    
    intros.
    inversion H2; subst.
    specialize (eval_type_reserve _ _ _ _ _ H H0 H9); intros h1.
    specialize (eval_type_reserve _ _ _ _ _ H H1 H10); intros h2.    
    destruct v1 as [v11 | v12]; destruct v2 as [v21 | v22]; 
    inversion h1; subst; try rm_contradict. 
  - (* Ebinop Tint Tint *)
    destruct op; try simpl_binop_hyp;
    [ br_rm_rop (Int v11) (Int v21) Zeq_bool v11 v21 |
      br_rm_rop (Int v11) (Int v21) Zneq_bool v11 v21 |
      br_rm_aop (Int v11) (Int v21) (v11 + v21)%Z |
      br_rm_aop (Int v11) (Int v21) (v11 - v21)%Z |
      br_rm_aop (Int v11) (Int v21) (v11 * v21)%Z |
      br_rm_aop (Int v11) (Int v21) (v11 / v21)%Z
    ]; rm_exists;
    [br_clearer (Bool x) good_value | br_clearer (Bool x) good_value | | | | ];
    br_clearer (Int x) good_value.
  - (* Ebinop Tbool Tbool *)
    destruct op; 
    simpl; 
    try simpl_binop_hyp.
    br_clearer (Bool (v12 && v22)) eval_binop.    
    br_clearer (Bool (v12 || v22)) eval_binop.   
Qed.

Ltac ru_rm_unop v1 v2 :=
    match goal with
    [ |- exists b : value, eval_expr _ (Eunop ?ast_id ?uop ?e) (ValNormal b)] => 
            assert (exists b, eval_unop uop (ValNormal v1) = ValNormal (Bool b)) 
    end; 
    [simpl_unop; exists v2; auto | ].

Ltac ur_clearer v :=
    exists v;
    eapply eval_Eunop; eassumption.   


Lemma unop_rule: forall tb s e v ast_id op t,
    type_check_stack tb s -> 
    eval_expr s e (ValNormal v) ->
    well_typed_expr tb (Eunop ast_id op e) t -> 
    (exists bv : value, eval_expr s (Eunop ast_id op e) (ValNormal bv)).
Proof.
    intros.
    inversion H1; subst.
    specialize (eval_type_reserve _ _ _ _ _ H H0 H6); 
    intros h1.
    destruct v; try rm_contradict.
    destruct op.
    ru_rm_unop (Bool b) (negb b).
    rm_exists.  
    ur_clearer (Bool x).
Qed.

(** * Correctness Proof About Well-Formed Expression *)

Lemma well_formed_expr: forall tb s istate e t,
    type_check_stack tb s -> 
    initializationMap s istate ->
    well_defined_expr istate e ->
    well_typed_expr tb e t ->
    exists v, eval_expr s e v /\ return_value_type v t.
Proof.
    intros tb s istate e t h1 h2 h3.
    generalize t. 
    induction h3; 
    intros t0 h4.
  - (* 1. Econst_Int *)
    exists (ValNormal (Int n)).
    split.
    + constructor. 
       unfold eval_constant; simpl; auto.
    + inversion h4; subst.
       constructor.
  - (* 2. Econst_Bool *)
    exists (ValNormal (Bool b)).
    split.
    + constructor. 
       unfold eval_constant; simpl; auto.
    + inversion h4; subst.
       constructor.
  - (* 3. Evar *)
    specialize (initializationMap_consistent2 _ _ _ h2 H); intros hz1.
    inversion hz1.
    exists (ValNormal x0). 
    put_in_context_as hz2. (* this one is used to prove "return_value_type _ _" *)
    constructor; assumption.
    split.
    + assumption.
    + apply eval_type_reserve with (s := s) (tb := tb) (e := (Evar ast_id x));
       assumption.
  - (* 4. Ebinop *)
    assert (hz1: exists v, eval_expr s (Ebinop ast_id op e1 e2) v). (* this one is used to prove "return_value_type _ _" *)
    inversion h4; subst. 
    specialize (IHh3_1 h2 _ H5).
    specialize (IHh3_2 h2 _ H6).
    rm_exists.
    destruct x; destruct x0.
    + specialize (binop_rule _ _ _ _ _ _ _ _ _ h1 H1 H0 h4); intros hz2.
       rm_exists. 
       exists (ValNormal x); assumption.
    + specialize (exceptionVal_has_no_typ _ _ _ _ h1 H1 H5); intuition.
    + specialize (exceptionVal_has_no_typ _ _ _ _ h1 H0 H6); intuition.
    + specialize (exceptionVal_has_no_typ _ _ _ _ h1 H0 H6); intuition.
    
    + rm_exists. 
       exists x. 
       split; try assumption.
       apply eval_type_reserve with (s := s) (tb := tb) (e := (Ebinop ast_id op e1 e2));
       assumption.
  - (* 5. Eunop *)
    assert(hz1: exists v, eval_expr s (Eunop ast_id op e) v ). (* this one is used to prove "return_value_type _ _" *)
    inversion h4; subst.
    specialize (IHh3 h2 _ H3).
    rm_exists.
    specialize (eval_type_reserve _ _ _ _ _ h1 H0 H3); intros hz2.
    destruct x; try rm_contradict.
    destruct v; try rm_contradict.
    set (y :=  (eval_unop op (ValNormal (Bool b)))).
    exists y. 
    econstructor. 
    apply H0. intuition.
    
    rm_exists.
    exists (x).
    split; try assumption.
    apply eval_type_reserve with (s := s) (tb := tb) (e := (Eunop ast_id op e));
    assumption.
Qed.


(* = = = = = = = = = = = = = = =  *)
(* = = = = = = = = = = = = = = =  *)

(** some help lemmas *)
Lemma valid_update: forall tb s ast_id x e v,
    type_check_stack tb s ->
    well_typed_stmt tb (Sassign ast_id x e) ->
    exists s', update s x (Value v) = Some s'.  (* !!! *)
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

Lemma type_reserve: forall s x v s' tb m t ,
    update s x (Value v) = Some s' ->    
    type_check_stack tb s -> 
    lookup x tb = Some (m, t)-> 
    return_value_type (ValNormal v) t ->
    type_check_stack tb s'. (* !!! *)
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

Lemma type_reserve_assign: forall tb s ast_id x e v s',
    type_check_stack tb s -> 
    well_typed_stmt tb (Sassign ast_id x e) -> 
    eval_expr s e (ValNormal v) ->
    update s x (Value v) = Some s' ->
    type_check_stack tb s'. (* !!! *)
Proof.
    intros tb s ast_id x e v s' h1 h2 h3 h4.
    inversion h2; subst.
    specialize (eval_type_reserve _ _ _ _ _ h1 h3 H4); intros hz1.
    specialize (type_reserve _ _ _ _ _ _ _ h4 h1 H2 hz1); intros hz2.
    assumption.
Qed.

Lemma symbol_consistent_reserve: forall tb s c s',
    type_check_stack tb s -> 
    well_typed_stmt tb c ->
    eval_stmt s c s' ->  (* the assignment does not check the type consistency *)
    type_check_stack tb s'. (* !!! *)
Proof.
    intros tb s c s' h1 h2 h3.
    induction h3.
  - (* Sassign *)
    specialize (type_reserve_assign _ _ _ _ _ _ _ h1 h2 H H0); intros hz1.
    assumption.
  - inversion h2; subst.
    apply IHh3_2.
    apply IHh3_1;
    assumption.
    assumption.
  - inversion h2; subst.
    apply IHh3;
    assumption.
  - inversion h2; subst.
    assumption.
  - inversion h2; subst.
    apply IHh3_2.
    apply IHh3_1;
    assumption.
    assumption.
  - inversion h2; subst.
    assumption.
Qed.


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

Lemma eval_stmt_greater: forall s c s' istate istate' istate1,
     eval_stmt s c s' -> 
     initializationMap s istate ->
     well_defined_stmt istate c istate' -> 
     initializationMap s' istate1 -> 
     (forall x, (fetch2 x istate' = Some Init -> fetch2 x istate1 = Some Init) /\
                   (fetch2 x istate' = Some Uninit -> exists m, fetch2 x istate1 = Some m)).
Proof.
    intros s c s' istate istate' istate1 h1.
    generalize istate istate' istate1.
    clear istate istate' istate1.
    induction h1;
    intros istate istate' istate1 h2 h3 h4.
  - (* 1. Sassign *)
    inversion h3; subst.
    specialize (update_consis _ _ _ _ _ _ _ h2 H0 H7 h4); intros hz1.
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
    specialize (IHh1_1 _ _ _ h2 H4 H).
    assert (hz2: exists istate, well_defined_stmt x c2 istate).
    specialize (initializationMap_stmt _ _ _ _ H5 IHh1_1); intros hz2.
    assumption.
    rm_exists.
    specialize (IHh1_2 _ _ _ H H0 h4).
    specialize (wd_fetch2_sync _ _ _ _ _ H5 H0 IHh1_1); intros hz3.
    specialize (fetch2_transitive _ _ _ hz3 IHh1_2); intros hz4.
    assumption.
  - (* 3. Sifthen_true *)
    inversion h3; subst.
    specialize (IHh1 _ _ _ h2 H6 h4).
    specialize (initializationMap_inc _ _ _ H6); intros hz1.
    specialize (fetch2_transitive _ _ _ hz1 IHh1); intros hz2.
    assumption.
  - (* 4. Sifthen_false *)
    inversion h3; subst.
    specialize (initializationMap_unique _ _ _ h4 h2); intros hz3.
    subst.
    intros x.
    split; intros hz.
    + assumption.
    + exists Uninit; assumption.
  - (* 5. Swhile_true *)
    inversion h3; subst.
    specialize (imap_exists s1); intros hz1.
    rm_exists.
    specialize (IHh1_1 _ _ _ h2 H6 H0).
    specialize (initializationMap_inc _ _ _ H6); intros hz2.
    assert (hz2': exists istate, well_defined_stmt x (Swhile ast_id b c) istate).
    exists x.
    assert (hz3: exists istate, well_defined_stmt x c istate).
    specialize (initializationMap_stmt _ _ _ _ H6 hz2); intros hz3.
    inversion hz3.
    specialize (initializationMap_stmt _ _ _ _ H1 IHh1_1); intros hz4.    
    assumption.
    inversion hz3.
    apply WD_Swhile with (s' := x0). 
    + specialize (fetch2_transitive _ _ _ hz2 IHh1_1); intros hz5.
       specialize (initializationMap_expr1 _ _ _ H5 hz5); intros hz6.
       assumption.
    + assumption.
    + inversion hz2'.
       inversion H1; subst.
       specialize (IHh1_2 _ _ _ H0 H1 h4).
       specialize (fetch2_transitive _ _ _ IHh1_1 IHh1_2); intros hz3.
       specialize (fetch2_transitive _ _ _ hz2 hz3); intros hz4.
       assumption.
  - (* 6. Swhile_false *)
    inversion h3; subst.
    specialize (initializationMap_unique _ _ _ h4 h2); intros hz3.
    subst.
    intros x.
    split; intros hz.
    + assumption.
    + exists Uninit; assumption.
Qed.

Lemma initializationMap_consistent: forall s istate c1 s' istate' c2 istate'' istate1,
     initializationMap s istate ->
     eval_stmt s c1 s' -> 
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


Ltac unfold_f_eval_stmt :=
    match goal with
    | [ |- context[f_eval_stmt ?k ?s _]] => unfold f_eval_stmt; simpl
    end.


(** * Correctness Proof About Well-Formed Command *)

(* do functional induction on 'f_eval_stmt k s c', so 'k, s, c' are put before the other variables in the 
    universal qualifier. 
 *)
Lemma well_formed_cmd: forall k s c tb istate istate', 
    well_typed_stmt tb c -> 
    type_check_stack tb s ->
    initializationMap s istate ->
    well_defined_stmt istate c istate' ->
    (exists s', f_eval_stmt k s c = (SNormal s')) \/ f_eval_stmt k s c = SUnterminated.
Proof.
    intros k s c.
    functional induction (f_eval_stmt k s c);
    intros.
  - right; auto.
  - left.
    exists s1; auto.
  - (* proof term with contradictory hypothesis *)
    inversion H; subst.
    inversion H2; subst.
    specialize (typed_value' _ _ _ _ _ H0 H6); intros hz1.
    inversion hz1.
    clear hz1 H H0 H1 H2 H4 H6 H8 H10 H11 e2.
    functional induction (reside x s).
    + unfold update in e3.
       rewrite e1 in e3.
       inversion e3.
    + unfold update in e3.
       rewrite e1 in e3.
       fold update in e3.
       destruct (update s' x (Value v)).
       * inversion e3.
       * apply  IHb; auto.
    + inversion H3.
  - (* proof term with contradictory hypothesis *)
    inversion H; subst.
    inversion H2; subst.
    specialize (well_formed_expr _ _ _ _ _ H0 H1 H10 H8); intros hz2.
    rm_exists.
    specialize (f_eval_expr_complete _ _ _ H4); intros hz3.
    rewrite hz3 in e2.
    destruct x0.
    + inversion e2.
    + inversion H5.
  - (* Sseq*)
    inversion H; subst.
    inversion H2; subst.
    specialize (f_eval_stmt_correct _ _ _ _ e1); intros hz1.
    specialize (symbol_consistent_reserve _ _ _ _ H0 H6 hz1); intros hz2.
    specialize (imap_exists s1); intros hz3.
    inversion hz3.
    assert (hz4: exists istate, well_defined_stmt x c2 istate).
    { specialize (eval_stmt_greater _ _ _ _ _ _ hz1 H1 H10 H3); intros hz5.
      specialize (initializationMap_stmt _ _ _ _ H11 hz5); intros hz6.
      assumption.
    }
    inversion hz4.
    specialize (IHs1 _ _ _ H8 hz2 H3 H4).
    assumption.
  - (* proof term with contradictory hypothesis *)
    inversion H; subst.
    inversion H2; subst.
    specialize (IHs0 _ _ _ H6 H0 H1 H10).
    rewrite e1 in IHs0.
    inversion IHs0.
    + inversion H3. 
       inversion H4.
    + inversion H3.
  - right; auto.
  - (* Sifthen_True *)
    inversion H; subst.
    inversion H2; subst.
    specialize (IHs0 _ _ _ H8 H0 H1 H11).
    assumption.
  - left.
    exists s; auto.
  - (* proof term with contradictory hypothesis *)
    inversion H; subst.
    inversion H2; subst.
    specialize (well_formed_expr _ _ _ _ _ H0 H1 H10 H6); intros hz2.
    rm_exists.
    specialize (f_eval_expr_complete _ _ _ H4); intros hz3.
    rewrite hz3 in y.
    destruct x. 
    + destruct v. 
       inversion H5. 
       destruct b0; inversion y.
    + inversion H5.
  - (* Swhile_True *)
    inversion H; subst.
    inversion H2; subst.
    specialize (f_eval_stmt_correct _ _ _ _ e2); intros hz1.
    specialize (imap_exists s1); intros hz2.
    rm_exists.
    assert (hz3: well_defined_stmt x (Swhile ast_id b c0) x).
    { specialize (initializationMap_inc _ _ _ H11); intros hz2.
      specialize (eval_stmt_greater _ _ _ _ _ _ hz1 H1 H11 H3); intros hz3.
      specialize (fetch2_transitive _ _ _ hz2 hz3); intros hz4.
      specialize (initializationMap_stmt _ _ _ _ H2 hz4); intros hz5.
      inversion hz5.
      inversion H4; subst.
      assumption.
    }
    specialize (symbol_consistent_reserve _ _ _ _ H0 H8 hz1); intros hz4.
    specialize (IHs1 _ _ _ H hz4 H3 hz3).
    assumption.
  - (* proof term with contradictory hypothesis *)
    inversion H; subst.
    inversion H2; subst.
    specialize (IHs0 _ _ _ H8 H0 H1 H11).
    rewrite e2 in IHs0.
    inversion IHs0.
    + inversion H3.
       inversion H4.
    + inversion H3.
  - right; auto.
  - left.
    exists s; auto.
  - (* proof term with contradictory hypothesis *)
    inversion H; subst.
    inversion H2; subst.
    specialize (well_formed_expr _ _ _ _ _ H0 H1 H10 H6); intros hz2.
    rm_exists.
    specialize (f_eval_expr_complete _ _ _ H4); intros hz3.
    rewrite hz3 in y.
    destruct x. 
    + destruct v. 
       inversion H5. 
       destruct b0; inversion y.
    + inversion H5.    
Qed.



