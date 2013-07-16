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
    constructor.
  - constructor.  
  - (* Evar *)
    specialize (typed_value _ _ i v h1 ); intros hz1.
    specialize (hz1 H6).
    rm_exists.
    rewrite H3 in H. inversion H; subst.
    apply value_type_consistent; assumption.
  - (* Ebinop *)
    specialize (IHe1 _ _ h1 H14 H5).
    specialize (IHe2 _ _ h1 H15 H6).
    destruct v1 as [v11 | v12]; inversion IHe1; subst;
    destruct v2 as [v21 | v22]; try rm_contradict.
    + destruct b; 
       repeat simpl_binop_hyp; 
       inversion H17; subst; constructor.
    + destruct b; try simpl_binop_hyp;
       inversion H17; subst; constructor.
  - (* Eunop *)
    destruct op; destruct v0; inversion H9; subst.
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
    constructor.
  - constructor.  
  - (* Evar *)
    specialize (typed_value _ _ i v h1 ); intros hz1.
    specialize (hz1 H6).
    rm_exists.
    rewrite H3 in H. inversion H; subst.
    apply value_type_consistent; assumption.
  - (* Ebinop *)
    specialize (IHe1 _ _ h1 H14 H5).
    specialize (IHe2 _ _ h1 H15 H6).
    destruct v1 as [v11 | v12]; inversion IHe1; subst;
    destruct v2 as [v21 | v22]; try rm_contradict.
    + destruct b; 
       repeat simpl_binop_hyp;
       inversion H18; subst; constructor.
    + destruct b; try simpl_binop_hyp;
       inversion H18; subst; constructor.
  - specialize (IHe1 _ _ h1 H14 H5).
    specialize (IHe2 _ _ h1 H15 H6).
    destruct v1 as [v11 | v12]; inversion IHe1; subst;
    destruct v2 as [v21 | v22]; try rm_contradict.
    + destruct b; 
       repeat simpl_binop_hyp;
       inversion H17; subst; constructor.
    + destruct b; try simpl_binop_hyp;
       inversion H17; subst; constructor.
  - (* Eunop *)
    destruct op; destruct v0; inversion H9; subst.
    constructor.
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

(** * Correctness Proof About Well-Formed Command *)

(** 
    subset is introduced to prove eval_expr_with_checks_correct and eval_stmt_with_checks_correct, 
    otherwise they cannot be proved directly 
*)
Definition subset (n: astnum) (cks1: check_points) (cks2: check_points): Prop := 
    forall id v, 
    id < n -> 
    fetch_ck id cks1 = v -> 
    fetch_ck id cks2 = v.

Lemma subset_refl: forall n ls,
    subset n ls ls.
Proof.
    intros.
    unfold subset; intros.
    assumption.
Qed.


Lemma subset_close: forall n0 n ls1 ls2,
    subset n0 ls1 ls2 ->
    n < n0 ->
    subset n ls1 ls2.
Proof.
    intros.
    unfold subset in *.
    intros.
    apply H;
    intuition.
Qed. 

Lemma subset_close_le: forall n0 n ls1 ls2,
    subset n0 ls1 ls2 ->
    n <= n0 ->
    subset n ls1 ls2.
Proof.
    intros.
    unfold subset in *.
    intros.
    apply H;
    intuition.
Qed. 

Lemma subset_close1: forall ls0 ls1 ast_id flag,
    subset ast_id ((ast_id, flag) :: ls0) ls1 ->
    subset ast_id ls0 ls1.
Proof.
    intros.
    unfold subset in *.
    intros.
    apply H.
    assumption.
    specialize (lt_not_equal _ _ H0); intros hz1.
    unfold fetch_ck.
    rewrite hz1; fold fetch_ck.
    assumption.
Qed.


Lemma subset_trans: forall n0 n1 cks0 cks1 cks2,
    subset n0 cks0 cks1 ->
    subset n1 cks1 cks2 ->
    n0 < n1 ->
    subset n0 cks0 cks2.
Proof.
    intros.
    unfold subset in *.
    intros.
    apply H0. 
    intuition.
    apply H; assumption.
Qed.

Lemma subset_trans_le: forall n0 n1 cks0 cks1 cks2,
    subset n0 cks0 cks1 ->
    subset n1 cks1 cks2 ->
    n0 <= n1 ->
    subset n0 cks0 cks2.
Proof.
    intros.
    unfold subset in *.
    intros.
    apply H0. 
    intuition.
    apply H; assumption.
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
    subset (get_ast_id_expr e) cks0 cks1.
Proof.
    intros cks0 e cks1 max h1 h2.
    revert max.
    induction h1; simpl in h2;
    intros max h3;
    inversion h3; subst;
    try apply subset_refl; simpl.
  - specialize (ast_ids_lt_trans _ _ _ h2 H9); intros hz1.
    specialize (ast_ids_lt_trans _ _ _ h2 H10); intros hz2.
    specialize (ast_ids_lt_add _ _ _ flag H9 hz1); intros hz3.
    specialize (IHh1_1 hz3 _ H4).
    specialize (lt_trans_expr _ _ _ _ _ h1_1 hz3 H4 H11); intros hz4.
    specialize (IHh1_2 hz4 _ H5).
    specialize (subset_close _ _ _ _ IHh1_1 H9); intros hz5.
    specialize (subset_close1 _ _ _ _ hz5); intros hz6.
    specialize (subset_trans _ _ _ _ _ hz6 IHh1_2 H10); auto.
  - specialize (ast_ids_lt_trans _ _ _ h2 H9); intros hz1.
    specialize (ast_ids_lt_trans _ _ _ h2 H10); intros hz2.
    specialize (IHh1_1 hz1 _ H4).
    specialize (lt_trans_expr _ _ _ _ _ h1_1 hz1 H4 H11); intros hz3.
    specialize (IHh1_2 hz3 _ H5).
    specialize (ast_id_bound_expr _ _ H4); intros hz4.
    assert (hz5: get_ast_id_expr e1 < get_ast_id_expr e2); intuition.
    specialize (subset_trans _ _ _ _ _ IHh1_1 IHh1_2 hz5); intros hz6.
    specialize (subset_close _ _ _ _ hz6 H9); intuition.
  - specialize (ast_ids_lt_trans _ _ _ h2 H4); intros hz1.
    specialize (IHh1 hz1 _ H1).
    specialize (subset_close _ _ _ _ IHh1 H4); intuition.
Qed.


(** it's similar to subset_expr *)
Lemma subset_stmt: forall cks0 c cks1 max,
    check_generator_stmt cks0 c cks1 ->
    ast_ids_lt cks0 (get_ast_id_stmt c) -> 
    ast_id_inc_stmt c max ->
    subset (get_ast_id_stmt c) cks0 cks1.
Proof.
    intros cks0 c cks1 max h1.
    revert max.
    induction h1; 
    intros max h2 h3;
    simpl in h2; inversion h3; subst;
    simpl.
  - (* Sassign *)
    specialize (ast_ids_lt_trans _ _ _ h2 H6); intros hz1.
    specialize (subset_expr _ _ _ _ H hz1 H3); intros hz2.
    apply subset_close with (n0 := get_ast_id_expr e); assumption.
  - (* Sseq *)
    specialize (ast_ids_lt_trans _ _ _ h2 H6); intros hz1.
    specialize (IHh1_1 _ hz1 H2).
    specialize (ast_id_max_stmt _ _ _ _ H2 h1_1 hz1); intros hz2.
    assert (hz: max1 + 1 <= get_ast_id_stmt c2); intuition.
    specialize (ast_ids_lt_trans0 _ _ _ hz2 hz); intros hz3.
    specialize (IHh1_2 _ hz3 H3).
    specialize (ast_id_bound_stmt _ _ H2); intros hz4.
    assert (hz5: get_ast_id_stmt c1 < get_ast_id_stmt c2); intuition.
    specialize (subset_trans _ _ _ _ _ IHh1_1 IHh1_2 hz5); intros hz6.
    specialize (subset_close _ _ _ _ hz6 H6); auto.
  - (* Sifthen *)
    specialize (ast_ids_lt_trans _ _ _ h2 H7); intros hz1.
    specialize (ast_id_max_expr _ _ _ _ H3 H hz1); intros hz2.
    assert (hz: max1 + 1 <= get_ast_id_stmt c); intuition.
    specialize (ast_ids_lt_trans0 _ _ _ hz2 hz); intros hz3.
    specialize (IHh1 _ hz3 H4).
    specialize (subset_expr _ _ _ _ H hz1 H3); intros hz4.
    specialize (ast_id_bound_expr _ _ H3); intros hz5.
    assert (hz6: get_ast_id_expr b < get_ast_id_stmt c); intuition.
    specialize (subset_trans _ _ _ _ _ hz4 IHh1 hz6); intros hz7.
    apply subset_close with (n0 := (get_ast_id_expr b)); auto.
  - (* Swhile *)
    specialize (ast_ids_lt_trans _ _ _ h2 H7); intros hz1.
    specialize (ast_id_max_expr _ _ _ _ H3 H hz1); intros hz2.
    assert (hz: max1 + 1 <= get_ast_id_stmt c); intuition.
    specialize (ast_ids_lt_trans0 _ _ _ hz2 hz); intros hz3.
    specialize (IHh1 _ hz3 H4).
    specialize (subset_expr _ _ _ _ H hz1 H3); intros hz4.
    specialize (ast_id_bound_expr _ _ H3); intros hz5.
    assert (hz6: get_ast_id_expr b < get_ast_id_stmt c); intuition.
    specialize (subset_trans _ _ _ _ _ hz4 IHh1 hz6); intros hz7.
    apply subset_close with (n0 := (get_ast_id_expr b)); auto.
Qed.


(** 
    help1 and help2 are just help lemmas that are used repeatedly to prove eval_expr_with_checks_correct0, 
    so I define them as lemmas
*)

Lemma help1: forall ls0 ls1 ls2 e max n,
    check_generator_expr ls0 e ls1 ->
    ast_id_inc_expr e max ->
    ast_ids_lt ls0 (get_ast_id_expr e) ->
    n < get_ast_id_expr e ->
    subset (max + 1) ls1 ls2 ->
    subset (n + 1) ls0 ls2.
Proof.
    intros.
    specialize (subset_expr _ _ _ _ H H1 H0); intros hz1.
    specialize (ast_id_bound_expr _ _ H0); intros hz2.
    assert (hz3: (get_ast_id_expr e) < (max + 1)); intuition.
    specialize (subset_trans _ _ _ _ _ hz1 H3 hz3); intros hz4.
    assert (hz5: n + 1 <= get_ast_id_expr e); intuition.
    specialize (subset_close_le _ _ _ _ hz4 hz5); 
    intuition.
Qed.

Lemma help2: forall ls0 ls1 ls2 c max n,
    check_generator_stmt ls0 c ls1 ->
    ast_id_inc_stmt c max ->
    ast_ids_lt ls0 (get_ast_id_stmt c) ->
    n < get_ast_id_stmt c ->
    subset (max + 1) ls1 ls2 ->
    subset (n + 1) ls0 ls2.
Proof.
    intros.
    specialize (subset_stmt _ _ _ _ H H1 H0); intros hz1.
    specialize (ast_id_bound_stmt _ _ H0); intros hz2.
    assert (hz3: (get_ast_id_stmt c) < (max + 1)); intuition.
    specialize (subset_trans _ _ _ _ _ hz1 H3 hz3); intros hz4.
    assert (hz5: n + 1 <= get_ast_id_stmt c); intuition.
    specialize (subset_close_le _ _ _ _ hz4 hz5); 
    intuition.
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
    subset (max + 1) cks1 cks ->
    check_generator_expr cks0 e cks1 ->
    ast_ids_lt cks0 (get_ast_id_expr e) ->
    ast_id_inc_expr e max ->
    eval_expr s e v.
Proof.
    intros cks s e v cks1 cks0 max h1.
    revert cks1 cks0 max.
    induction h1;
    intros cks1 cks0 max h2 h3 h4 h5;
    simpl in h4;
    inversion h5; subst.
  - (* Econst *) 
    constructor; auto.
  - (* Evar *)
    constructor; auto.
  - (* Ebinop *)
    inversion h3; subst.
    + specialize (ast_ids_lt_trans _ _ _ h4 H8); intros hz1. 
       specialize (ast_ids_lt_add _ _ _ flag H8 hz1); intros hz2.       
       specialize (lt_trans_expr _ _ _ _ _ H11 hz2 H3 H10); intros hz3.
       specialize (help1 _ _ _ _ _ _ H12 H4 hz3 H10 h2); intros hz4.       
       specialize (IHh1 _ _ _ hz4 H11 hz2 H3).
       constructor; assumption.
    + specialize (ast_ids_lt_trans _ _ _ h4 H8); intros hz1.
       specialize (lt_trans_expr _ _ _ _ _ H11 hz1 H3 H10); intros hz2.
       specialize (help1 _ _ _ _ _ _ H12 H4 hz2 H10 h2); intros hz3.
       specialize (IHh1 _ _ _ hz3 H11 hz1 H3).
       constructor; assumption.
  - inversion h3; subst.
    + specialize (ast_ids_lt_trans _ _ _ h4 H8); intros hz1.
       specialize (ast_ids_lt_add _ _ _ flag H8 hz1); intros hz2.
       specialize (lt_trans_expr _ _ _ _ _ H11 hz2 H3 H10); intros hz3.
       specialize (help1 _ _ _ _ _ _ H12 H4 hz3 H10 h2); intros hz4.
       specialize (IHh1_1 _ _ _ hz4 H11 hz2 H3).
       specialize (IHh1_2 _ _ _ h2 H12 hz3 H4).
       eapply eval_Ebinop2. 
       apply IHh1_1.
       assumption.
    + specialize (ast_ids_lt_trans _ _ _ h4 H8); intros hz1.
       specialize (lt_trans_expr _ _ _ _ _ H11 hz1 H3 H10); intros hz2.
       specialize (help1 _ _ _ _ _ _ H12 H4 hz2 H10 h2); intros hz3.
       specialize (IHh1_1 _ _ _ hz3 H11 hz1 H3).
       specialize (IHh1_2 _ _ _ h2 H12 hz2 H4).       
       eapply eval_Ebinop2. 
       apply IHh1_1.
       assumption.
  - inversion h3; subst.
    + specialize (ast_ids_lt_trans _ _ _ h4 H10); intros hz1.
       specialize (ast_ids_lt_add _ _ _ flag H10 hz1); intros hz2.
       specialize (lt_trans_expr _ _ _ _ _ H13 hz2 H5 H12); intros hz3.
       specialize (help1 _ _ _ _ _ _ H14 H6 hz3 H12 h2); intros hz4.
       specialize (IHh1_1 _ _ _ hz4 H13 hz2 H5).
       specialize (IHh1_2 _ _ _ h2 H14 hz3 H6).
       eapply eval_Ebinop3. 
       apply IHh1_1. apply IHh1_2.
       assumption.
    + specialize (ast_ids_lt_trans _ _ _ h4 H10); intros hz1.
       specialize (lt_trans_expr _ _ _ _ _ H13 hz1 H5 H12); intros hz2.
       specialize (help1 _ _ _ _ _ _ H14 H6 hz2 H12 h2); intros hz3.
       specialize (IHh1_1 _ _ _ hz3 H13 hz1 H5).
       specialize (IHh1_2 _ _ _ h2 H14 hz2 H6).
       eapply eval_Ebinop3. 
       apply IHh1_1. apply IHh1_2.
       assumption.
  - inversion h3; subst.
    + specialize (ast_ids_lt_trans _ _ _ h4 H11); intros hz1.
       specialize (ast_ids_lt_add _ _ _ flag H11 hz1); intros hz2.
       specialize (lt_trans_expr _ _ _ _ _ H14 hz2 H6 H13); intros hz3.
       specialize (help1 _ _ _ _ _ _ H15 H7 hz3 H13 h2); intros hz4.
       specialize (IHh1_1 _ _ _ hz4 H14 hz2 H6).
       specialize (IHh1_2 _ _ _ h2 H15 hz3 H7).
       eapply eval_Ebinop4. 
       apply IHh1_1. apply IHh1_2.
       assumption. assumption.
    + specialize (ast_ids_lt_trans _ _ _ h4 H11); intros hz1.
       specialize (lt_trans_expr _ _ _ _ _ H14 hz1 H6 H13); intros hz2.
       specialize (help1 _ _ _ _ _ _ H15 H7 hz2 H13 h2); intros hz3.
       specialize (IHh1_1 _ _ _ hz3 H14 hz1 H6).
       specialize (IHh1_2 _ _ _ h2 H15 hz2 H7).
       eapply eval_Ebinop4. 
       apply IHh1_1. apply IHh1_2.
       assumption. assumption.
  - inversion h3; subst.     
    + specialize (ast_ids_lt_trans _ _ _ h4 H10); intros hz1.
       specialize (ast_ids_lt_add _ _ _ flag H10 hz1); intros hz2.
       specialize (lt_trans_expr _ _ _ _ _ H13 hz2 H5 H12); intros hz3.
       specialize (help1 _ _ _ _ _ _ H14 H6 hz3 H12 h2); intros hz4.
       specialize (IHh1_1 _ _ _ hz4 H13 hz2 H5).
       specialize (IHh1_2 _ _ _ h2 H14 hz3 H6).
       eapply eval_Ebinop4. 
       apply IHh1_1. apply IHh1_2.
       specialize (subset_expr _ _ _ _ H13 hz2 H5); intros hz5.
       assert(A1: get_ast_id_expr e1 < max1 + 1).
       specialize (ast_id_bound_expr _ _ H5); intros ha2.
       intuition.
       specialize (subset_trans _ _ _ _ _ hz5 hz4 A1); intros hz6.
       unfold subset in hz6. 
       specialize (hz6 ast_id (Some flag)).
       unfold fetch_ck in hz6.
       rewrite <- (beq_nat_refl ast_id) in hz6. fold fetch_ck in hz6.
       intuition. 
       rewrite H in H2; inversion H2.
       assumption.
    + specialize (ast_ids_lt_trans _ _ _ h4 H10); intros hz1.
       specialize (lt_trans_expr _ _ _ _ _ H13 hz1 H5 H12); intros hz2.
       specialize (help1 _ _ _ _ _ _ H14 H6 hz2 H12 h2); intros hz3.
       specialize (IHh1_1 _ _ _ hz3 H13 hz1 H5).
       specialize (IHh1_2 _ _ _ h2 H14 hz2 H6).
       eapply eval_Ebinop4. 
       apply IHh1_1. apply IHh1_2.
       
       destruct op; inversion H9; subst;
       constructor; assumption.       
       assumption.
  - (* Eunop *)
    inversion h3; subst.
    specialize (ast_ids_lt_trans _ _ _ h4 H4); intros hz1.
    specialize (IHh1 _ _ _ h2 H5 hz1 H1).
    econstructor; assumption.
  - inversion h3; subst.
    specialize (ast_ids_lt_trans _ _ _ h4 H5); intros hz1.
    specialize (IHh1 _ _ _ h2 H6 hz1 H2).
    econstructor. 
    apply IHh1.
    assumption.
Qed.


(** ** eval_expr_with_checks_correct *)
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
    specialize (subset_refl (max + 1) cks); intros hz1.
    specialize (eval_expr_with_checks_correct0 _ _ _ _ _ _ _ H hz1 H0 H1 H2).
    auto.
Qed.


(** 
    Because we cannot prove eval_stmt_with_checks_correct directly, so 
    eval_stmt_with_checks_correct0 is proved as an intermediate proof step by introducing "subset",
    it's similar to eval_expr_with_checks_correct0
*)
Theorem eval_stmt_with_checks_correct_0: forall cks s c s' cks1 cks0 max,
    eval_stmt_with_checks cks s c s' ->
    subset (max + 1) cks1 cks ->
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
    specialize (eval_expr_with_checks_correct0 _ _ _ _ _ _ _ H h2 H5 hz1 H9); intros hz2.
    constructor;
    assumption.
  - specialize (ast_ids_lt_trans _ _ _ h4 H13); intros hz1.
    specialize (eval_expr_with_checks_correct0 _ _ _ _ _ _ _ H h2 H6 hz1 H10); intros hz2.
    econstructor.
    apply hz2.
    assumption.
  - (* Sseq *)
    specialize (ast_ids_lt_trans _ _ _ h4 H13); intros hz1.
    specialize (lt_trans_stmt _ _ _ _ _ H4 hz1 H9 H16); intros hz2.
    specialize (help2 _ _ _ _ _ _ H5 H10 hz2 H16 h2); intros hz3.
    specialize (IHh1 _ _ _ hz3 H4 hz1 H9).
    constructor; assumption.
  - specialize (ast_ids_lt_trans _ _ _ h4 H13); intros hz1.
    specialize (lt_trans_stmt _ _ _ _ _ H4 hz1 H9 H16); intros hz2.
    specialize (help2 _ _ _ _ _ _ H5 H10 hz2 H16 h2); intros hz3.
    specialize (IHh1_1 _ _ _ hz3 H4 hz1 H9).
    specialize (IHh1_2 _ _ _ h2 H5 hz2 H10).
    econstructor.
    apply IHh1_1.
    assumption.
  - (* Sifthen *)
    specialize (ast_ids_lt_trans _ _ _ h4 H14); intros hz1.
    specialize (lt_trans_expr _ _ _ _ _ H5 hz1 H10 H17); intros hz2.
    specialize (help2 _ _ _ _ _ _ H6 H11 hz2 H17 h2); intros hz3.
    specialize (eval_expr_with_checks_correct0 _ _ _ _ _ _ _ H hz3 H5 hz1 H10); intros hz4.
    constructor; 
    assumption.
  - specialize (ast_ids_lt_trans _ _ _ h4 H14); intros hz1.
    specialize (lt_trans_expr _ _ _ _ _ H5 hz1 H10 H17); intros hz2.
    specialize (help2 _ _ _ _ _ _ H6 H11 hz2 H17 h2); intros hz3.
    specialize (eval_expr_with_checks_correct0 _ _ _ _ _ _ _ H hz3 H5 hz1 H10); intros hz4.
    specialize (IHh1 _ _ _ h2 H6 hz2 H11).
    econstructor; try assumption. 
  - specialize (ast_ids_lt_trans _ _ _ h4 H14); intros hz1.
    specialize (lt_trans_expr _ _ _ _ _ H5 hz1 H10 H17); intros hz2.
    specialize (help2 _ _ _ _ _ _ H6 H11 hz2 H17 h2); intros hz3.
    specialize (eval_expr_with_checks_correct0 _ _ _ _ _ _ _ H hz3 H5 hz1 H10); intros hz4.
    apply eval_Sifthen_False; assumption.
  - (* Swhile *)
    specialize (ast_ids_lt_trans _ _ _ h4 H14); intros hz1.
    specialize (lt_trans_expr _ _ _ _ _ H5 hz1 H10 H17); intros hz2.
    specialize (help2 _ _ _ _ _ _ H6 H11 hz2 H17 h2); intros hz3.
    specialize (eval_expr_with_checks_correct0 _ _ _ _ _ _ _ H hz3 H5 hz1 H10); intros hz4.
    constructor; 
    assumption.   
  - specialize (ast_ids_lt_trans _ _ _ h4 H14); intros hz1.
    specialize (lt_trans_expr _ _ _ _ _ H5 hz1 H10 H17); intros hz2.
    specialize (help2 _ _ _ _ _ _ H6 H11 hz2 H17 h2); intros hz3.
    specialize (eval_expr_with_checks_correct0 _ _ _ _ _ _ _ H hz3 H5 hz1 H10); intros hz4.
    specialize (IHh1 _ _ _ h2 H6 hz2 H11).
    eapply eval_Swhile_True1; try assumption.
  - specialize (ast_ids_lt_trans _ _ _ h4 H14); intros hz1.
    specialize (lt_trans_expr _ _ _ _ _ H5 hz1 H10 H17); intros hz2.
    specialize (help2 _ _ _ _ _ _ H6 H11 hz2 H17 h2); intros hz3.
    specialize (eval_expr_with_checks_correct0 _ _ _ _ _ _ _ H hz3 H5 hz1 H10); intros hz4.
    specialize (IHh1_1 _ _ _ h2 H6 hz2 H11).
    specialize (IHh1_2 _ _ _ h2 h3 h4 h5).
    eapply eval_Swhile_True2; auto.
    apply IHh1_1. apply IHh1_2.
  - specialize (ast_ids_lt_trans _ _ _ h4 H14); intros hz1.
    specialize (lt_trans_expr _ _ _ _ _ H5 hz1 H10 H17); intros hz2.
    specialize (help2 _ _ _ _ _ _ H6 H11 hz2 H17 h2); intros hz3.
    specialize (eval_expr_with_checks_correct0 _ _ _ _ _ _ _ H hz3 H5 hz1 H10); intros hz4.
    eapply eval_Swhile_False; auto.
Qed.

(** ** eval_stmt_with_checks_correct *)
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
    specialize (subset_refl (max + 1) cks); intros hz1.
    specialize (eval_stmt_with_checks_correct_0 _ _ _ _ _ _ _ H hz1 H0 H1 H2).
    auto.
Qed.

