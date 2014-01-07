(** 
_AUTHOR_

<<
Zhi Zhang
Departmnt of Computer and Information Sciences
Kansas State University
zhangzhi@ksu.edu
>>
*)

Require Export util.
Require Export wellformedness.
Require Export semantics.
Require Export typing.

(** * Properties Proof *)

(** help tactics used to prove other lemmas *)
Ltac simpl_binop_hyp :=
    repeat match goal with
    | [h: Some ?T = binop_type ?OP ?T1 ?T1 |- _ ] => 
            unfold binop_type in h; simpl in h; inversion h; subst
    | [h: binop_type ?OP ?T1 ?T1 = Some ?T |- _ ] => 
            unfold binop_type in h; simpl in h; inversion h; subst
    | [h: Val_Normal ?V = f_eval_bin_expr ?OP _ _ |- _] =>
            unfold f_eval_bin_expr in h; simpl in h; inversion h; subst
    | [h: f_eval_bin_expr ?OP _ _ = Val_Normal ?V |- _] =>
            unfold f_eval_bin_expr in h; simpl in h; inversion h; subst
    end.

Ltac rm_contradict := 
    match goal with
    | [h: value_of_type (Bool _) Integer |- _ ] =>  inversion h
    | [h: value_of_type (Int _) Boolean |- _ ] =>  inversion h
    | [h: Some ?T = binop_type ?OP Integer Boolean |- _ ] => unfold binop_type in h; simpl in h; inversion h
    | [h: Some ?T = binop_type ?OP Boolean Integer |- _ ] => unfold binop_type in h; simpl in h; inversion h
    end.


(** the type of the expression evaluation result should be consistent 
    with the type computed by the type checker;
*)
Lemma eval_type_reserve: forall tb s e v t,
    type_check_store tb s -> 
    eval_expr s e (Val_Normal v) ->
    well_typed_expr tb e t ->
    value_of_type v t.
Proof.
    intros tb s e.
    induction e;
    intros v t h1 h2 h3;
    inversion h3;
    inversion h2; subst.
  - (* E_Literal *)
    constructor.
  - constructor.  
  - (* E_Identifier *)
    specialize (typed_value _ _ i v h1 ); intros hz1.
    specialize (hz1 H6).
    rm_exists.
    rewrite H3 in H. inversion H; subst.
    assumption.
  - (* E_Binary_Operation *)
    specialize (IHe1 _ _ h1 H14 H5).
    specialize (IHe2 _ _ h1 H15 H6).
    destruct v1 as [v11 | v12]; inversion IHe1; subst;
    destruct v2 as [v21 | v22]; try rm_contradict.
    + destruct b; 
       repeat simpl_binop_hyp; 
       inversion H17; subst; constructor.
    + destruct b; try simpl_binop_hyp;
       inversion H17; subst; constructor.
  - (* E_Unary_Operation *)
    destruct op; destruct v0; inversion H9; subst.
    constructor.
Qed.

(** type of the evaluation result computed by eval_expr_with_checks 
    should be consistent with the type computed by the type checker;
    the difference between eval_expr and eval_expr_with_checks is that:
    eval_expr has checks performed implicitly according to the language 
    semantics, while eval_expr_with_checks performs checks only if there 
    are check flags requiring to do that;
*)
Lemma eval_type_reserve2: forall tb s cks e v t,
    type_check_store tb s -> 
    eval_expr_with_checks cks s e (Val_Normal v) ->
    well_typed_expr tb e t ->
    value_of_type v t.
Proof.
    intros tb s cks e.
    induction e;
    intros v t h1 h2 h3;
    inversion h3;
    inversion h2; subst.
  - (* E_Literal *)
    constructor.
  - constructor.  
  - (* E_Identifier *)
    specialize (typed_value _ _ i v h1 ); intros hz1.
    specialize (hz1 H6).
    rm_exists.
    rewrite H3 in H. inversion H; subst.
    assumption.
  - (* E_Binary_Expression *)
    specialize (IHe1 _ _ h1 H14 H5).
    specialize (IHe2 _ _ h1 H15 H6).
    destruct v1 as [v11 | v12]; inversion IHe1; subst;
    destruct v2 as [v21 | v22]; try rm_contradict.
    + destruct b; 
       repeat simpl_binop_hyp;
       inversion H18; subst; constructor.
    + destruct b; try simpl_binop_hyp;
       inversion H18; subst; constructor.
  - (* E_Unary_Expression *)
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

(** * Correctness Proof About Well-Formed Statement *)

(** 
    _subset_ is introduced to prove eval_expr_with_checks_correct and 
    eval_stmt_with_checks_correct, otherwise they cannot be proved directly;
    check_points is a kind of mapping from ast number to check flags labled
    for that ast node, and we say that cks1 is a subset of cks2 with respect
    to the number n iff forall index less than n, cks1 and cks2 have the same
    check flags;
*)
Definition subset (n: astnum) (cks1: check_points) (cks2: check_points): Prop := 
    forall id v, 
    id < n -> 
    fetch_cks id cks1 = v -> 
    fetch_cks id cks2 = v.

Lemma subset_refl: forall n ls,
    subset n ls ls.
Proof.
    intros.
    unfold subset; intros.
    assumption.
Qed.

(** "subset n0 ls1 ls2" means that for any index less than n0, if 
    there is a check flag in ls1, then there exists the same check
    flag in ls2; so for any n less than n0, "subset n ls1 ls2" is
    also satisfied;
*)
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

Lemma subset_close1: forall ls0 ls1 ast_num flag,
    subset ast_num ((ast_num, flag) :: ls0) ls1 ->
    subset ast_num ls0 ls1.
Proof.
    intros.
    unfold subset in *.
    intros.
    apply H.
    assumption.
    specialize (lt_not_equal _ _ H0); intros hz1.
    unfold fetch_cks.
    rewrite hz1; fold fetch_cks.
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
    if all ast id numbers in checks list ls is less then n, in other 
    words, n is outside the domain of ls, then when we fetch n from 
    ls, of course it returns None;
*)
Lemma fetch_cks_none: forall ls n,
    ast_nums_lt ls n ->
    fetch_cks n ls = nil.
Proof.
    intros.
    induction H.
    + simpl. 
       remember (beq_nat n ast_num) as b.
       destruct b.
       * symmetry in Heqb. 
         apply beq_nat_true in Heqb; rewrite Heqb in H0.
         omega.
      * assumption.
    + auto.
Qed.

(** 
    if ast_num is not in cks0, and ast_num is less than all ast numbers 
    used in expression e, and cks1 is the resulting check list generated 
    for expression e with ast numbers as its index, then ast_num is not 
    in cks1;
*)
Lemma fetch_cks_none1: forall ast_num cks0 e cks1 max,
    fetch_cks ast_num cks0 = nil -> 
    check_generator_expr cks0 e cks1 ->
    ast_num_inc_expr e max -> 
    ast_num < (get_ast_num_expr e) ->
    fetch_cks ast_num cks1 = nil.
Proof.
    intros ast_num cks0 e cks1 max h1 h2.
    revert max.
    induction h2;
    intros max h3 h4;
    simpl in h4; inversion h3; subst; auto.
  - assert (hz1: ast_num < get_ast_num_expr e1); intuition.
    assert (hz2: ast_num < get_ast_num_expr e2); intuition.
    specialize (H0 _ H4 hz1).
    specialize (IHh2_2 H0 _ H5 hz2).
    assumption.
  - assert (hz1: fetch_cks ast_num ((ast_num0, cks) :: ls) = nil).
    unfold fetch_cks. 
    rewrite (lt_not_equal _ _ h4). assumption. 
    assert (hz2: ast_num < get_ast_num_expr e1); intuition.
    assert (hz3: ast_num < get_ast_num_expr e2); intuition.
    specialize (H1 _ H5 hz2).
    specialize (IHh2_2 H1 _ H6 hz3).
    assumption.
  - assert (hz1: ast_num < get_ast_num_expr e); intuition.
    specialize (H _ H1 hz1).
    assumption.
Qed.


(** 
    cks1 is a list of checks that are generated for expression e on top 
    of cks0, if max is the maximum ast number used inside e and all ast 
    numbers in cks0 are less than ast numbers used in e, then for any n 
    greater than max, n should be greater than all ast numbers stored in 
    cks1;
*)
Lemma lt_trans_expr: forall cks0 cks1 e max n,
    check_generator_expr cks0 e cks1 ->
    ast_nums_lt cks0 (get_ast_num_expr e) ->
    ast_num_inc_expr e max ->
    max < n ->
    ast_nums_lt cks1 n.
Proof.
    intros.
    specialize (ast_num_max_expr _ _ _ _ H1 H H0); intros h1.
    assert (h2: max + 1 <= n); intuition.
    specialize (ast_nums_lt_trans0 _ _ _ h1 h2); intros h3.
    assumption.
Qed.

(* it's similar to lt_trans_expr *)
Lemma lt_trans_stmt: forall cks0 cks1 c max n,
    check_generator_stmt cks0 c cks1 ->
    ast_nums_lt cks0 (get_ast_num_stmt c) ->
    ast_num_inc_stmt c max ->
    max < n ->
    ast_nums_lt cks1 n.
Proof.
    intros.
    specialize (ast_num_max_stmt _ _ _ _ H1 H H0); intros h1.
    assert (h2: max + 1 <= n); intuition.
    specialize (ast_nums_lt_trans0 _ _ _ h1 h2); intros h3.
    assumption.
Qed.

Lemma lt_trans_decl: forall cks0 cks1 d max n,
    check_generator_decl cks0 d cks1 ->
    ast_nums_lt cks0 d.(declaration_astnum) ->
    ast_num_inc_decl d max ->
    max < n ->
    ast_nums_lt cks1 n.
Proof.
    intros.
    specialize (ast_num_max_decl _ _ _ _ H1 H H0); intros hz1.
    assert (hz2: max + 1 <= n); intuition.
    specialize (ast_nums_lt_trans0 _ _ _ hz1 hz2);
    auto.
Qed.

Lemma lt_trans_decls: forall tl cks0 cks1 d max n,
    check_generator_decls cks0 (d :: tl) cks1 ->
    ast_nums_lt cks0 d.(declaration_astnum) ->
    ast_num_inc_decls (d :: tl) max ->
    max < n ->
    ast_nums_lt cks1 n.
Proof.
    induction tl; intros;
    inversion H; subst;
    inversion H1; subst.
  - inversion H8; subst.
    specialize (lt_trans_decl _ _ _ _ _ H6 H0 H4 H2); auto.
  - specialize (lt_trans_decl _ _ _ _ _ H6 H0 H7 H10); intros hz1.
    specialize (IHtl _ _ _ _ _ H8 hz1 H11 H2).
    assumption.
Qed.


(** 
    cks1 is a list of checks that are generated for expression e on top 
    of cks0, so cks1 should be a superset of cks0;
    ast_num_inc_expr enforces that all ast numbers used in e are unique 
    and increasing, and ast_num_lt constrains that all ast numbers in cks0 
    are smaller than the ast numbers used in e, this is an implicit requirement 
    enforced by check_generator_expr, for example: 
    for binary expression "e1 op e2", [check_generator_expr nil (e1 op e2) cks1] 
    can be computed by first computing [check_generator_expr nil e1 cks0] and 
    then computing [check_generator_expr cks0 e2 cks1], because the ast numbers 
    are increasing inside the expression, so all ast numbers in cks0 should be 
    smaller than the ast numbers in e2;
*)
Lemma subset_expr: forall cks0 e cks1 max,
    check_generator_expr cks0 e cks1 ->
    ast_nums_lt cks0 (get_ast_num_expr e) -> (* ensure that all ast num used in e is fresh *)
    ast_num_inc_expr e max -> (* ensure that all ast numbers are unique and increasing *)
    subset (get_ast_num_expr e) cks0 cks1.
Proof.
    intros cks0 e cks1 max h1 h2.
    revert max.
    induction h1; simpl in h2;
    intros max h3;
    inversion h3; subst;
    try apply subset_refl; simpl.
  - specialize (ast_nums_lt_trans _ _ _ h2 H9); intros hz1.
    specialize (ast_nums_lt_trans _ _ _ h2 H10); intros hz2.
    specialize (IHh1_1 hz1 _ H4).
    specialize (lt_trans_expr _ _ _ _ _ h1_1 hz1 H4 H11); intros hz3.
    specialize (IHh1_2 hz3 _ H5).
    specialize (ast_num_bound_expr _ _ H4); intros hz4.
    assert (hz5: get_ast_num_expr e1 < get_ast_num_expr e2); intuition.
    specialize (subset_trans _ _ _ _ _ IHh1_1 IHh1_2 hz5); intros hz6.
    specialize (subset_close _ _ _ _ hz6 H9); intuition.
  - specialize (ast_nums_lt_trans _ _ _ h2 H10); intros hz1.
    specialize (ast_nums_lt_trans _ _ _ h2 H11); intros hz2.
    specialize (ast_nums_lt_add _ _ _ cks H10 hz1); intros hz3.
    specialize (IHh1_1 hz3 _ H5).
    specialize (lt_trans_expr _ _ _ _ _ h1_1 hz3 H5 H12); intros hz4.
    specialize (IHh1_2 hz4 _ H6).
    specialize (subset_close _ _ _ _ IHh1_1 H10); intros hz5.
    specialize (subset_close1 _ _ _ _ hz5); intros hz6.
    specialize (subset_trans _ _ _ _ _ hz6 IHh1_2 H11); auto.
  - specialize (ast_nums_lt_trans _ _ _ h2 H4); intros hz1.
    specialize (IHh1 hz1 _ H1).
    specialize (subset_close _ _ _ _ IHh1 H4); intuition.
Qed.


(** it's similar to subset_expr *)
Lemma subset_stmt: forall cks0 c cks1 max,
    check_generator_stmt cks0 c cks1 ->
    ast_nums_lt cks0 (get_ast_num_stmt c) -> 
    ast_num_inc_stmt c max ->
    subset (get_ast_num_stmt c) cks0 cks1.
Proof.
    intros cks0 c cks1 max h1.
    revert max.
    induction h1; 
    intros max h2 h3;
    simpl in h2; inversion h3; subst;
    simpl.
  - (* Sassign *)
    specialize (ast_nums_lt_trans _ _ _ h2 H6); intros hz1.
    specialize (subset_expr _ _ _ _ H hz1 H3); intros hz2.
    apply subset_close with (n0 := get_ast_num_expr e); assumption.
  - (* Sseq *)
    specialize (ast_nums_lt_trans _ _ _ h2 H6); intros hz1.
    specialize (IHh1_1 _ hz1 H2).
    specialize (ast_num_max_stmt _ _ _ _ H2 h1_1 hz1); intros hz2.
    assert (hz: max1 + 1 <= get_ast_num_stmt c2); intuition.
    specialize (ast_nums_lt_trans0 _ _ _ hz2 hz); intros hz3.
    specialize (IHh1_2 _ hz3 H3).
    specialize (ast_num_bound_stmt _ _ H2); intros hz4.
    assert (hz5: get_ast_num_stmt c1 < get_ast_num_stmt c2); intuition.
    specialize (subset_trans _ _ _ _ _ IHh1_1 IHh1_2 hz5); intros hz6.
    specialize (subset_close _ _ _ _ hz6 H6); auto.
  - (* Sifthen *)
    specialize (ast_nums_lt_trans _ _ _ h2 H7); intros hz1.
    specialize (ast_num_max_expr _ _ _ _ H3 H hz1); intros hz2.
    assert (hz: max1 + 1 <= get_ast_num_stmt c); intuition.
    specialize (ast_nums_lt_trans0 _ _ _ hz2 hz); intros hz3.
    specialize (IHh1 _ hz3 H4).
    specialize (subset_expr _ _ _ _ H hz1 H3); intros hz4.
    specialize (ast_num_bound_expr _ _ H3); intros hz5.
    assert (hz6: get_ast_num_expr b < get_ast_num_stmt c); intuition.
    specialize (subset_trans _ _ _ _ _ hz4 IHh1 hz6); intros hz7.
    apply subset_close with (n0 := (get_ast_num_expr b)); auto.
  - (* Swhile *)
    specialize (ast_nums_lt_trans _ _ _ h2 H7); intros hz1.
    specialize (ast_num_max_expr _ _ _ _ H3 H hz1); intros hz2.
    assert (hz: max1 + 1 <= get_ast_num_stmt c); intuition.
    specialize (ast_nums_lt_trans0 _ _ _ hz2 hz); intros hz3.
    specialize (IHh1 _ hz3 H4).
    specialize (subset_expr _ _ _ _ H hz1 H3); intros hz4.
    specialize (ast_num_bound_expr _ _ H3); intros hz5.
    assert (hz6: get_ast_num_expr b < get_ast_num_stmt c); intuition.
    specialize (subset_trans _ _ _ _ _ hz4 IHh1 hz6); intros hz7.
    apply subset_close with (n0 := (get_ast_num_expr b)); auto.
Qed.


Lemma subset_decl: forall cks0 d cks1 max,
    check_generator_decl cks0 d cks1 ->
    ast_nums_lt cks0 d.(declaration_astnum) -> 
    ast_num_inc_decl d max ->
    subset d.(declaration_astnum) cks0 cks1.
Proof.
    intros cks0 d cks1 max h1.
    revert max.
    induction h1; 
    intros max h2 h3.
  - apply subset_refl.
  - inversion h3; subst.
    rewrite <- H in H2; inversion H2; subst;
    specialize (ast_nums_lt_trans _ _ _ h2 H5); intros hz1.
    specialize (subset_expr _ _ _ _ H0 hz1 H3); intros hz2.
    specialize (subset_close _ _ _ _ hz2 H5); intros hz3.
    assumption.
    rewrite <- H in H2; inversion H2.
Qed.

Lemma subset_decls: forall tl cks0 d cks1 max,
    check_generator_decls cks0 (d :: tl) cks1 ->
    ast_nums_lt cks0 d.(declaration_astnum) -> 
    ast_num_inc_decls (d :: tl) max ->
    subset d.(declaration_astnum) cks0 cks1.
Proof.
    induction tl; intros;
    inversion H; subst;
    inversion H1; subst.
  - inversion H7; subst.
    specialize (subset_decl _ _ _ _ H5 H0 H3); auto.
  - specialize (lt_trans_decl _ _ _ _ _ H5 H0 H6 H9); intros hz1.
    specialize (IHtl _ _ _ _ H7 hz1 H10).
    specialize (subset_decl _ _ _ _ H5 H0 H6); intros hz2.
    specialize (ast_num_bound_decl _ _ H6); intros hz3.
    assert (hz4: declaration_astnum d < declaration_astnum a); intuition.
    specialize (subset_trans _ _ _ _ _ hz2 IHtl hz4); auto.
Qed.

(** 
    help1, help2 and help3 are just help lemmas that are used 
    repeatedly to prove eval_expr_with_checks_correct0 and other 
    lemmas, so they are defined as helper lemmas;
*)

Lemma help1: forall ls0 ls1 ls2 e max n,
    check_generator_expr ls0 e ls1 ->
    ast_num_inc_expr e max ->
    ast_nums_lt ls0 (get_ast_num_expr e) ->
    n < get_ast_num_expr e ->
    subset (max + 1) ls1 ls2 ->
    subset (n + 1) ls0 ls2.
Proof.
    intros.
    specialize (subset_expr _ _ _ _ H H1 H0); intros hz1.
    specialize (ast_num_bound_expr _ _ H0); intros hz2.
    assert (hz3: (get_ast_num_expr e) < (max + 1)); intuition.
    specialize (subset_trans _ _ _ _ _ hz1 H3 hz3); intros hz4.
    assert (hz5: n + 1 <= get_ast_num_expr e); intuition.
    specialize (subset_close_le _ _ _ _ hz4 hz5); 
    intuition.
Qed.

Lemma help2: forall ls0 ls1 ls2 c max n,
    check_generator_stmt ls0 c ls1 ->
    ast_num_inc_stmt c max ->
    ast_nums_lt ls0 (get_ast_num_stmt c) ->
    n < get_ast_num_stmt c ->
    subset (max + 1) ls1 ls2 ->
    subset (n + 1) ls0 ls2.
Proof.
    intros.
    specialize (subset_stmt _ _ _ _ H H1 H0); intros hz1.
    specialize (ast_num_bound_stmt _ _ H0); intros hz2.
    assert (hz3: (get_ast_num_stmt c) < (max + 1)); intuition.
    specialize (subset_trans _ _ _ _ _ hz1 H3 hz3); intros hz4.
    assert (hz5: n + 1 <= get_ast_num_stmt c); intuition.
    specialize (subset_close_le _ _ _ _ hz4 hz5); 
    intuition.
Qed.

Lemma help3: forall ls0 ls1 ls2 d max n,
    check_generator_decl ls0 d ls1 ->
    ast_num_inc_decl d max ->
    ast_nums_lt ls0 d.(declaration_astnum) ->
    n < d.(declaration_astnum)->
    subset (max + 1) ls1 ls2 ->
    subset (n + 1) ls0 ls2.
Proof.
    intros.
    specialize (subset_decl _ _ _ _ H H1 H0); intros hz1.
    specialize (ast_num_bound_decl _ _ H0); intros hz2.
    assert (hz3: d.(declaration_astnum) < (max + 1)); intuition.
    specialize (subset_trans _ _ _ _ _ hz1 H3 hz3); intros hz4.
    assert (hz5: n + 1 <= d.(declaration_astnum)); intuition.
    specialize (subset_close_le _ _ _ _ hz4 hz5); 
    intuition.
Qed.


Lemma fetch_cks_inv: forall e flags cks0 cks1 max,
    check_flags e flags ->
    check_generator_expr cks0 e cks1 ->
    ast_nums_lt cks0 (get_ast_num_expr e) ->
    ast_num_inc_expr e max ->
    fetch_cks (get_ast_num_expr e) cks1 = flags.
Proof.
    intros e flags cks0 cks1 max h1.
    revert cks0 cks1 max.
    induction h1;
    intros cks0 cks1 max h2 h3 h4;
    simpl in *; 
    match goal with
    | h: check_generator_expr ?cks0 (E_Literal _ _) ?cks1 |- _ => 
        inversion h2; subst; apply fetch_cks_none; auto
    | h: check_generator_expr ?cks0 (E_Identifier _ _ ) ?cks1 |- _ =>
        inversion h2; subst; apply fetch_cks_none; auto
    | _ => inversion h4; subst
    end.
  - (* E_Binary_Operation: Plus *)
    inversion h2; subst.
    inversion H7; subst; rm_false_hyp.
    inversion H6; subst.
    assert (hz1: ast_nums_lt ((ast_num, Do_Overflow_Check :: nil) :: cks0) (get_ast_num_expr e1)).
      apply ast_nums_lt_add; auto.
      apply ast_nums_lt_trans with (n := ast_num); auto.
    assert (hz2: subset (get_ast_num_expr e1) ((ast_num, Do_Overflow_Check :: nil) :: cks0) ls1).
      apply subset_expr with (max := max1); auto.
    assert (hz3: subset (get_ast_num_expr e2) ls1 cks1).
      apply subset_expr with (max := max); auto.
      apply lt_trans_expr with (cks0 := ((ast_num, Do_Overflow_Check :: nil) :: cks0)) (e := e1) (max := max1);
      auto.
    apply hz3; auto.
    apply hz2; auto.
    simpl. rewrite <- beq_nat_refl. auto.
    rm_false_hyp.
  - (* E_Binary_Operation: Minus *)
    inversion h2; subst.
    inversion H7; subst; rm_false_hyp.
    inversion H6; subst.
    assert (hz1: ast_nums_lt ((ast_num, Do_Overflow_Check :: nil) :: cks0) (get_ast_num_expr e1)).
      apply ast_nums_lt_add; auto.
      apply ast_nums_lt_trans with (n := ast_num); auto.
    assert (hz2: subset (get_ast_num_expr e1) ((ast_num, Do_Overflow_Check :: nil) :: cks0) ls1).
      apply subset_expr with (max := max1); auto.
    assert (hz3: subset (get_ast_num_expr e2) ls1 cks1).
      apply subset_expr with (max := max); auto.
      apply lt_trans_expr with (cks0 := ((ast_num, Do_Overflow_Check :: nil) :: cks0)) (e := e1) (max := max1);
      auto.
    apply hz3; auto.
    apply hz2; auto.
    simpl. rewrite <- beq_nat_refl. auto.
    rm_false_hyp.
  - (* E_Binary_Operation: Multiply *)
    inversion h2; subst.
    inversion H7; subst; rm_false_hyp.
    inversion H6; subst.
    assert (hz1: ast_nums_lt ((ast_num, Do_Overflow_Check :: nil) :: cks0) (get_ast_num_expr e1)).
      apply ast_nums_lt_add; auto.
      apply ast_nums_lt_trans with (n := ast_num); auto.
    assert (hz2: subset (get_ast_num_expr e1) ((ast_num, Do_Overflow_Check :: nil) :: cks0) ls1).
      apply subset_expr with (max := max1); auto.
    assert (hz3: subset (get_ast_num_expr e2) ls1 cks1).
      apply subset_expr with (max := max); auto.
      apply lt_trans_expr with (cks0 := ((ast_num, Do_Overflow_Check :: nil) :: cks0)) (e := e1) (max := max1);
      auto.
    apply hz3; auto.
    apply hz2; auto.
    simpl. rewrite <- beq_nat_refl. auto.
    rm_false_hyp.
  - (* E_Binary_Operation: Divide *)
    inversion h2; subst.
    inversion H7; subst; rm_false_hyp.
    inversion H6; subst.
    assert (hz1: ast_nums_lt ((ast_num, Do_Division_Check :: Do_Overflow_Check :: nil) :: cks0) (get_ast_num_expr e1)).
      apply ast_nums_lt_add; auto.
      apply ast_nums_lt_trans with (n := ast_num); auto.
    assert (hz2: subset (get_ast_num_expr e1) ((ast_num, Do_Division_Check :: Do_Overflow_Check :: nil) :: cks0) ls1).
      apply subset_expr with (max := max1); auto.
    assert (hz3: subset (get_ast_num_expr e2) ls1 cks1).
      apply subset_expr with (max := max); auto.
      apply lt_trans_expr with (cks0 := ((ast_num, Do_Division_Check :: Do_Overflow_Check :: nil) :: cks0)) (e := e1) (max := max1);
      auto.
    apply hz3; auto.
    apply hz2; auto.
    simpl. rewrite <- beq_nat_refl. auto.
    rm_false_hyp.
  - inversion h2; subst.
    apply fetch_cks_none1 with (cks0 := ls1) (e := e2) (max := max); auto.
    apply fetch_cks_none1 with (cks0 := cks0) (e := e1) (max := max1); auto.
    apply fetch_cks_none; auto.
    destruct op; try rm_false_hyp;
    inversion H10; subst; rm_false_hyp.
  - (* E_Unary_Operation *)
    inversion h2; subst.
    apply fetch_cks_none1 with (cks0 := cks0) (e := e) (max := max); auto.
    apply fetch_cks_none; auto.
Qed.


(** 
    We cannot prove eval_expr_with_checks_correct directly, so
    eval_expr_with_checks_correct0 is proved as an intermediate proof 
    step by introducing "subset";
    it means that if cks1 are checks that are generated for expression 
    e on top of cks0, and cks is a superset of cks1, then whenever e 
    is evaluated to value v under checks cks, expression e can also be 
    evaluated to value v in relational semantics eval_expr;
    
    all checks for expression e appearing in cks1 also appear in cks, 
    cks has more checks than cks1 with respect to the index that is 
    greater than e's maximum ast number, so even if cks is 
    a superset of cks1, all these extra checks in cks cannot affect 
    the evaluation of expression e;
*)

Lemma eval_expr_with_checks_correct0: forall cks s e v cks1 cks0 max,
    eval_expr_with_checks cks s e v ->
    subset (max + 1) cks1 cks ->
    check_generator_expr cks0 e cks1 ->
    ast_nums_lt cks0 (get_ast_num_expr e) ->
    ast_num_inc_expr e max ->
    eval_expr s e v.
Proof.
    intros cks s e v cks1 cks0 max h1.
    revert cks1 cks0 max.
    induction h1;
    intros cks1 cks'0 max h2 h3 h4 h5;
    simpl in h4;
    inversion h5; subst.
  - (* Econst *) 
    constructor; auto.
  - (* Evar *)
    constructor; auto.
  - (* Ebinop *)
    inversion h3; subst.
    + specialize (ast_nums_lt_trans _ _ _ h4 H8); intros hz1.
       specialize (lt_trans_expr _ _ _ _ _ H11 hz1 H3 H10); intros hz2.
       specialize (help1 _ _ _ _ _ _ H12 H4 hz2 H10 h2); intros hz3.
       specialize (IHh1 _ _ _ hz3 H11 hz1 H3).
       constructor; assumption.
    + specialize (ast_nums_lt_trans _ _ _ h4 H8); intros hz1. 
       specialize (ast_nums_lt_add _ _ _ cks0 H8 hz1); intros hz2.  
       specialize (lt_trans_expr _ _ _ _ _ H12 hz2 H3 H10); intros hz3.
       specialize (help1 _ _ _ _ _ _ H13 H4 hz3 H10 h2); intros hz4. 
       specialize (IHh1 _ _ _ hz4 H12 hz2 H3).
       constructor; assumption.
  - inversion h3; subst.
    + specialize (ast_nums_lt_trans _ _ _ h4 H8); intros hz1.
       specialize (lt_trans_expr _ _ _ _ _ H11 hz1 H3 H10); intros hz2.
       specialize (help1 _ _ _ _ _ _ H12 H4 hz2 H10 h2); intros hz3.
       specialize (IHh1_1 _ _ _ hz3 H11 hz1 H3).
       specialize (IHh1_2 _ _ _ h2 H12 hz2 H4).
       eapply eval_E_Binary_Operation2. 
       apply IHh1_1.
       assumption.
    + specialize (ast_nums_lt_trans _ _ _ h4 H8); intros hz1.
       specialize (ast_nums_lt_add _ _ _ cks0 H8 hz1); intros hz2.
       specialize (lt_trans_expr _ _ _ _ _ H12 hz2 H3 H10); intros hz3.
       specialize (help1 _ _ _ _ _ _ H13 H4 hz3 H10 h2); intros hz4.
       specialize (IHh1_1 _ _ _ hz4 H12 hz2 H3).
       specialize (IHh1_2 _ _ _ h2 H13 hz3 H4).
       eapply eval_E_Binary_Operation2. 
       apply IHh1_1.
       assumption.
  - inversion h3; subst.
    + assert(ha: fetch_cks ast_num cks = nil).
        apply h2.
        specialize (ast_num_bound_expr _ _ H6); intuition.
        replace ast_num with (get_ast_num_expr (E_Binary_Operation ast_num op e1 e2)).
        apply fetch_cks_inv with (cks0 := cks'0) (max := max); auto.
        auto.
      rewrite ha in *.
      destruct op;
      inversion H0; subst.
    + assert(ha: fetch_cks ast_num cks = cks0).
        apply h2.
        specialize (ast_num_bound_expr _ _ H6); intuition.
        replace ast_num with (get_ast_num_expr (E_Binary_Operation ast_num op e1 e2)).
        apply fetch_cks_inv with (cks0 := cks'0) (max := max); auto.
        auto.
      rewrite ha in *.
      specialize (ast_nums_lt_trans _ _ _ h4 H10); intros hz1.
      specialize (ast_nums_lt_add _ _ _ cks0 H10 hz1); intros hz2.
      specialize (lt_trans_expr _ _ _ _ _ H13 hz2 H5 H12); intros hz3.
      specialize (help1 _ _ _ _ _ _ H14 H6 hz3 H12 h2); intros hz4.
      specialize (IHh1_1 _ _ _ hz4 H13 hz2 H5).
      specialize (IHh1_2 _ _ _ h2 H14 hz3 H6).
      eapply eval_E_Binary_Operation3. 
      apply IHh1_1. apply IHh1_2.
      specialize (do_complete_checks_correct _ _ _ _ _ _ _ _ H7 H0); auto.
  - inversion h3; subst.
    + assert(ha: fetch_cks ast_num cks = nil).
        apply h2.
        specialize (ast_num_bound_expr _ _ H7); intuition.
        replace ast_num with (get_ast_num_expr (E_Binary_Operation ast_num op e1 e2)).
        apply fetch_cks_inv with (cks0 := cks'0) (max := max); auto.
        auto.
      rewrite ha in *.
      specialize (ast_nums_lt_trans _ _ _ h4 H11); intros hz1.
      specialize (lt_trans_expr _ _ _ _ _ H10 hz1 H6 H13); intros hz2.
      specialize (help1 _ _ _ _ _ _ H14 H7 hz2 H13 h2); intros hz3.
      specialize (IHh1_1 _ _ _ hz3 H10 hz1 H6).
      specialize (IHh1_2 _ _ _ h2 H14 hz2 H7).
      eapply eval_E_Binary_Operation4. 
      apply IHh1_1. apply IHh1_2.
      specialize (do_complete_checks_correct _ _ _ _ _ _ _ _ H9 H0); auto.
      assumption.
    + assert(ha: fetch_cks ast_num cks = cks0).
        apply h2.
        specialize (ast_num_bound_expr _ _ H7); intuition.
        replace ast_num with (get_ast_num_expr (E_Binary_Operation ast_num op e1 e2)).
        apply fetch_cks_inv with (cks0 := cks'0) (max := max); auto.
        auto.
      rewrite ha in *.
      specialize (ast_nums_lt_trans _ _ _ h4 H11); intros hz1.
      specialize (ast_nums_lt_add _ _ _ cks0 H11 hz1); intros hz2.
      specialize (lt_trans_expr _ _ _ _ _ H14 hz2 H6 H13); intros hz3.
      specialize (help1 _ _ _ _ _ _ H15 H7 hz3 H13 h2); intros hz4.
      specialize (IHh1_1 _ _ _ hz4 H14 hz2 H6).
      specialize (IHh1_2 _ _ _ h2 H15 hz3 H7).
      eapply eval_E_Binary_Operation4. 
      apply IHh1_1. apply IHh1_2.
      specialize (do_complete_checks_correct _ _ _ _ _ _ _ _ H8 H0); auto.
      assumption.
  - (* Eunop *)
    inversion h3; subst.
    specialize (ast_nums_lt_trans _ _ _ h4 H4); intros hz1.
    specialize (IHh1 _ _ _ h2 H5 hz1 H1).
    econstructor; assumption.
  - inversion h3; subst.
    specialize (ast_nums_lt_trans _ _ _ h4 H5); intros hz1.
    specialize (IHh1 _ _ _ h2 H6 hz1 H2).
    econstructor. 
    apply IHh1.
    assumption.
Qed.


(** ** eval_expr_with_checks_correct *)
(**
    cks is checks that are generated for expression e according to the 
    checking rules built on top of cks0, then whenever e is evaluated 
    to value v under checks cks, expression e can also be evaluated to 
    value v in relational semantics eval_expr;
    ast_num_inc_expr is used to constrain that all ast numbers used in 
    e are unique and increasing; 
    ast_nums_lt is used to enforce that index for new checks added for 
    expression e will not overlap the index used in cks0 built for 
    previous AST nodes;
*)
Theorem eval_expr_with_checks_correct: forall cks s e v cks0 max,
    eval_expr_with_checks cks s e v ->
    check_generator_expr cks0 e cks ->
    ast_nums_lt cks0 (get_ast_num_expr e) ->
    ast_num_inc_expr e max ->
    eval_expr s e v.
Proof.
    intros.
    specialize (subset_refl (max + 1) cks); intros hz1.
    specialize (eval_expr_with_checks_correct0 _ _ _ _ _ _ _ H hz1 H0 H1 H2).
    auto.
Qed.


(* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - *)

(**
    this is a help lemma to prove another lemma: eval_expr_with_checks_fixed;
    it means that: for any expression e, generate its checks according 
    to the checking rules and the results are stored in cks1, if cks1 
    is a subset of cks, and cks is a subset of cks', then, whenever e 
    is evaluated to a value v under the checks cks, e can also be evaluated 
    to value v under its superset cks';
    term "subset (max + 1) cks1 cks" means that: check list cks1 is a subset 
    of check list cks with respect to the index less than (max + 1), where 
    max is the maximum ast number used in expression e;
*)
Lemma eval_expr_with_checks_fixed0: forall cks s e v n cks' cks1 cks0 max,
    eval_expr_with_checks cks s e v ->
    max + 1 <= n ->
    subset n cks cks' ->
    (* the following four assumptions are necessary constraints for the proof *)
    subset (max + 1) cks1 cks ->
    check_generator_expr cks0 e cks1 ->
    ast_nums_lt cks0 (get_ast_num_expr e) ->
    ast_num_inc_expr e max ->  
    eval_expr_with_checks cks' s e v.
Proof.
    intros cks s e v  n cks' cks1 cks0 max h1.
    revert n cks' cks1 cks0 max.
    induction h1; intros n cks' cks1 cks'0 max h2 h3 h4 h5 h6 h7;
    simpl in h6; inversion h7; subst.
  - constructor; reflexivity.
  - constructor; assumption.
  - inversion h5; subst. 
    + specialize (ast_nums_lt_trans _ _ _ h6 H8); intros hz1. 
       specialize (lt_trans_expr _ _ _ _ _ H11 hz1 H3 H10); intros hz2.
       specialize (help1 _ _ _ _ _ _ H12 H4 hz2 H10 h4); intros hz3.
       assert (hz5: max1 + 1 <= n).
       specialize (ast_num_bound_expr _ _ H4); intros hz4; intuition.
       specialize (IHh1 _ _ _ _ _ hz5 h3 hz3 H11 hz1 H3).
       constructor; assumption.
    + specialize (ast_nums_lt_trans _ _ _ h6 H8); intros hz1.
       specialize (ast_nums_lt_add _ _ _ cks0 H8 hz1); intros hz2.
       specialize (lt_trans_expr _ _ _ _ _ H12 hz2 H3 H10); intros hz3.
       specialize (help1 _ _ _ _ _ _ H13 H4 hz3 H10 h4); intros hz4.
       assert (hz5: max1 + 1 <= n).
       specialize (ast_num_bound_expr _ _ H4); intros hz6. intuition.
       specialize (IHh1 _ _ _ _ _ hz5 h3 hz4 H12 hz2 H3).
       constructor; assumption.
  - inversion h5; subst.
    + specialize (ast_nums_lt_trans _ _ _ h6 H8); intros hz1.
       specialize (lt_trans_expr _ _ _ _ _ H11 hz1 H3 H10); intros hz2.
       specialize (help1 _ _ _ _ _ _ H12 H4 hz2 H10 h4); intros hz3.
       assert (hz4: max1 + 1 <= n).
       specialize (ast_num_bound_expr _ _ H4); intros hz5. intuition.
       specialize (IHh1_1 _ _ _ _ _ hz4 h3 hz3 H11 hz1 H3).
       specialize (IHh1_2 _ _ _ _ _ h2 h3 h4 H12 hz2 H4).
       eapply eval_Binary_Operation2.
       apply IHh1_1. apply IHh1_2.
    + specialize (ast_nums_lt_trans _ _ _ h6 H8); intros hz1.
       specialize (ast_nums_lt_add _ _ _ cks0 H8 hz1); intros hz2.
       specialize (lt_trans_expr _ _ _ _ _ H12 hz2 H3 H10); intros hz3.
       specialize (help1 _ _ _ _ _ _ H13 H4 hz3 H10 h4); intros hz4.
       assert (hz5: max1 + 1 <= n).
       specialize (ast_num_bound_expr _ _ H4); intros hz6. intuition.
       specialize (IHh1_1 _ _ _ _ _ hz5 h3 hz4 H12 hz2 H3).
       specialize (IHh1_2 _ _ _ _ _ h2 h3 h4 H13 hz3 H4).
       eapply eval_Binary_Operation2.
       apply IHh1_1. apply IHh1_2.
  - inversion h5; subst.
    + assert(ha: fetch_cks ast_num cks = nil).
        apply h4.
        specialize (ast_num_bound_expr _ _ H6); intuition.
        replace ast_num with (get_ast_num_expr (E_Binary_Operation ast_num op e1 e2)).
        apply fetch_cks_inv with (cks0 := cks'0) (max := max); auto.
        auto.
      rewrite ha in *.
      destruct op;
      inversion H0; subst.
    + assert(ha: fetch_cks ast_num cks = cks0).
        apply h4.
        specialize (ast_num_bound_expr _ _ H6); intuition.
        replace ast_num with (get_ast_num_expr (E_Binary_Operation ast_num op e1 e2)).
        apply fetch_cks_inv with (cks0 := cks'0) (max := max); auto.
        auto.
      rewrite ha in *.
      specialize (ast_nums_lt_trans _ _ _ h6 H10); intros hz1.
      specialize (ast_nums_lt_add _ _ _ cks0 H10 hz1); intros hz2.
      specialize (lt_trans_expr _ _ _ _ _ H13 hz2 H5 H12); intros hz3.
      specialize (help1 _ _ _ _ _ _ H14 H6 hz3 H12 h4); intros hz4.
      assert (hz5: max1 + 1 <= n).
      specialize (ast_num_bound_expr _ _ H6); intuition.
      specialize (IHh1_1 _ _ _ _ _ hz5 h3 hz4 H13 hz2 H5).
      specialize (IHh1_2 _ _ _ _ _ h2 h3 h4 H14 hz3 H6).
      eapply eval_Binary_Operation3.
      apply IHh1_1. apply IHh1_2.
      unfold subset in h3.
      assert (hz6: ast_num < n).
      specialize (ast_num_bound_expr _ _ H5); intuition.
      specialize (h3 _ _ hz6 ha).
      apply h3. assumption.
  - inversion h5; subst. 
    + assert(ha: fetch_cks ast_num cks = nil).
        apply h4.
        specialize (ast_num_bound_expr _ _ H7); intuition.
        replace ast_num with (get_ast_num_expr (E_Binary_Operation ast_num op e1 e2)).
        apply fetch_cks_inv with (cks0 := cks'0) (max := max); auto.
        auto.
      rewrite ha in *.
      specialize (ast_nums_lt_trans _ _ _ h6 H11); intros hz1.
      specialize (lt_trans_expr _ _ _ _ _ H10 hz1 H6 H13); intros hz2.
      specialize (help1 _ _ _ _ _ _ H14 H7 hz2 H13 h4); intros hz3.
      assert (hz4: max1 + 1 <= n).
      specialize (ast_num_bound_expr _ _ H7); intros hz5. intuition.
      specialize (IHh1_1 _ _ _ _ _ hz4 h3 hz3 H10 hz1 H6).
      specialize (IHh1_2 _ _ _ _ _ h2 h3 h4 H14 hz2 H7).
      eapply eval_Binary_Operation4.
      apply IHh1_1. apply IHh1_2.
      unfold subset in h3. 
      assert (hz5: ast_num < n).
      specialize (ast_num_bound_expr _ _ H6); intuition.
      specialize (h3 _ _ hz5 ha).
      apply h3. 
      assumption. assumption.
    + assert(ha: fetch_cks ast_num cks = cks0).
        apply h4.
        specialize (ast_num_bound_expr _ _ H7); intuition.
        replace ast_num with (get_ast_num_expr (E_Binary_Operation ast_num op e1 e2)).
        apply fetch_cks_inv with (cks0 := cks'0) (max := max); auto.
        auto.
      rewrite ha in *.
      specialize (ast_nums_lt_trans _ _ _ h6 H11); intros hz1.
      specialize (ast_nums_lt_add _ _ _ cks0 H11 hz1); intros hz2.
      specialize (lt_trans_expr _ _ _ _ _ H14 hz2 H6 H13); intros hz3.
      specialize (help1 _ _ _ _ _ _ H15 H7 hz3 H13 h4); intros hz4.
      assert (hz5: max1 + 1 <= n).
      specialize (ast_num_bound_expr _ _ H7); intros hz6. intuition.
      specialize (IHh1_1 _ _ _ _ _ hz5 h3 hz4 H14 hz2 H6).
      specialize (IHh1_2 _ _ _ _ _ h2 h3 h4 H15 hz3 H7).
      eapply eval_Binary_Operation4.
      apply IHh1_1. apply IHh1_2.
      unfold subset in h3. 
      assert (hz6: ast_num < n).
      specialize (ast_num_bound_expr _ _ H6); intuition.
      specialize (h3 _ _ hz6 ha).
      apply h3. 
      assumption. assumption.
  - inversion h5; subst. 
    specialize (ast_nums_lt_trans _ _ _ h6 H4); intros hz1. 
    specialize (IHh1 _ _ _ _ _ h2 h3 h4 H5 hz1 H1).
    constructor; assumption.
  - inversion h5; subst. 
    specialize (ast_nums_lt_trans _ _ _ h6 H5); intros hz1. 
    specialize (IHh1 _ _ _ _ _ h2 h3 h4 H6 hz1 H2).
    econstructor. 
    apply IHh1.
    assumption.
Qed.


(**
    for any expression e, generate its checks according to the checking rules and
    the results are stored in cks1, if cks1 is a subset of cks', then,
    whenever e is evaluated to a value v under the checks cks1, e can also be evaluated to 
    value v under its superset cks';
    term " subset (max + 1) cks1 cks' " means that: check list cks1 is a subset of check list cks' 
    with respect to the index less than (max + 1), where max is the maximum ast number used
    in expression e;
*)
Lemma eval_expr_with_checks_fixed: forall s e v cks' cks1 cks0 max,
    eval_expr_with_checks cks1 s e v ->
    subset (max + 1) cks1 cks' ->
    check_generator_expr cks0 e cks1 ->
    ast_nums_lt cks0 (get_ast_num_expr e) ->
    ast_num_inc_expr e max ->  
    eval_expr_with_checks cks' s e v.
Proof.
    intros.
    apply eval_expr_with_checks_fixed0 with (cks := cks1) (n := max + 1) (cks1 := cks1) (cks0 := cks0) (max := max); 
    auto.
    apply subset_refl.
Qed.

(**
    it's a help lemma used to prove the lemma: eval_stmt_with_checks_fixed;
    it's similar to eval_expr_with_checks_fixed0, the only difference is that: 
    eval_expre_with_checks_fixed0 is used for expression, and eval_stmt_with_checks_fixed0 is used for statement;
*)
Lemma eval_stmt_with_checks_fixed0: forall cks s0 c s1 n cks' cks1 cks0 max,
    eval_stmt_with_checks cks s0 c s1 ->
    max + 1 <= n ->
    subset n cks cks' ->
    (* the following four assumptions are necessary constraints for the proof *)
    subset (max + 1) cks1 cks ->
    check_generator_stmt cks0 c cks1 ->
    ast_nums_lt cks0 (get_ast_num_stmt c) ->
    ast_num_inc_stmt c max ->  
    eval_stmt_with_checks cks' s0 c s1.
Proof.
    intros cks s0 c s1 n cks' cks1 cks0 max h1.
    revert n cks' cks1 cks0 max.
    induction h1;
    intros n cks' cks1 cks0 max h2 h3 h4 h5 h6 h7;
    inversion h5; subst;
    simpl in h6;
    inversion h7; subst.
  - (* Sassign: SException *)
    specialize (ast_nums_lt_trans _ _ _ h6 H7); intros hz1.
    specialize (eval_expr_with_checks_fixed0 _ _ _ _ _ _ _ _ _ H h2 h3 h4 H5 hz1 H3); intros hz2.
    constructor; auto.
  - (* Sassign: SNormal *)
    specialize (ast_nums_lt_trans _ _ _ h6 H8); intros hz1.
    specialize (eval_expr_with_checks_fixed0 _ _ _ _ _ _ _ _ _ H h2 h3 h4 H6 hz1 H4); intros hz2.    
    econstructor.
    apply hz2. assumption.
  - (* Sseq: SException *)
    specialize (ast_nums_lt_trans _ _ _ h6 H8); intros hz1.
    specialize (lt_trans_stmt _ _ _ _ _ H4 hz1 H2 H11); intros hz2.
    assert (hz3: max1 + 1 <= n).
    specialize (ast_num_bound_stmt _ _ H3); intros ha1.
    intuition.
    specialize (help2 _ _ _ _ _ _ H5 H3 hz2 H11 h4); intros hz4.
    specialize (IHh1 _ _ _ _ _ hz3 h3 hz4 H4 hz1 H2).
    constructor; assumption.
  - (* Sseq *)
    specialize (ast_nums_lt_trans _ _ _ h6 H8); intros hz1.
    specialize (lt_trans_stmt _ _ _ _ _ H4 hz1 H2 H11); intros hz2.
    assert (hz3: max1 + 1 <= n).
    specialize (ast_num_bound_stmt _ _ H3); intros ha1.
    intuition.
    specialize (help2 _ _ _ _ _ _ H5 H3 hz2 H11 h4); intros hz4.
    specialize (IHh1_1 _ _ _ _ _ hz3 h3 hz4 H4 hz1 H2).
    specialize (IHh1_2 _ _ _ _ _ h2 h3 h4 H5 hz2 H3).
    eapply eval_Sequence2.
    apply IHh1_1.
    apply IHh1_2.
  - (* Sifthen: SException *)
    specialize (ast_nums_lt_trans _ _ _ h6 H9); intros hz1.
    specialize (lt_trans_expr _ _ _ _ _ H5 hz1 H3 H12); intros hz2.
    assert (hz3: max1 + 1 <= n).
    specialize (ast_num_bound_stmt _ _ H4); intros ha1.
    intuition.
    specialize (help2 _ _ _ _ _ _ H6 H4 hz2 H12 h4); intros hz4.
    specialize (eval_expr_with_checks_fixed0 _ _ _ _ _ _ _ _ _ H hz3 h3 hz4 H5 hz1 H3); intros hz5.
    constructor; assumption.
  - (* Sifthen: true branch *)
    specialize (ast_nums_lt_trans _ _ _ h6 H9); intros hz1.
    specialize (lt_trans_expr _ _ _ _ _ H5 hz1 H3 H12); intros hz2.
    assert (hz3: max1 + 1 <= n).
    specialize (ast_num_bound_stmt _ _ H4); intros ha1.
    intuition.
    specialize (help2 _ _ _ _ _ _ H6 H4 hz2 H12 h4); intros hz4.
    specialize (eval_expr_with_checks_fixed0 _ _ _ _ _ _ _ _ _ H hz3 h3 hz4 H5 hz1 H3); intros hz5.
    specialize (IHh1 _ _ _ _ _ h2 h3 h4 H6 hz2 H4).
    eapply eval_If_True; assumption.
  - (* Sifthen: false branch *)
    specialize (ast_nums_lt_trans _ _ _ h6 H9); intros hz1.
    specialize (lt_trans_expr _ _ _ _ _ H5 hz1 H3 H12); intros hz2.
    assert (hz3: max1 + 1 <= n).
    specialize (ast_num_bound_stmt _ _ H4); intros ha1.
    intuition.
    specialize (help2 _ _ _ _ _ _ H6 H4 hz2 H12 h4); intros hz4.
    specialize (eval_expr_with_checks_fixed0 _ _ _ _ _ _ _ _ _ H hz3 h3 hz4 H5 hz1 H3); intros hz5.
    eapply eval_If_False; assumption.
  - (* Swhile: SException at condition expression *)
    specialize (ast_nums_lt_trans _ _ _ h6 H9); intros hz1.
    specialize (lt_trans_expr _ _ _ _ _ H5 hz1 H3 H12); intros hz2.
    assert (hz3: max1 + 1 <= n).
    specialize (ast_num_bound_stmt _ _ H4); intros ha1.
    intuition.
    specialize (help2 _ _ _ _ _ _ H6 H4 hz2 H12 h4); intros hz4.
    specialize (eval_expr_with_checks_fixed0 _ _ _ _ _ _ _ _ _ H hz3 h3 hz4 H5 hz1 H3); intros hz5.
    constructor; assumption.
  - (* Swhile: SException at loop body *)
    specialize (ast_nums_lt_trans _ _ _ h6 H9); intros hz1.
    specialize (lt_trans_expr _ _ _ _ _ H5 hz1 H3 H12); intros hz2.
    assert (hz3: max1 + 1 <= n).
    specialize (ast_num_bound_stmt _ _ H4); intros ha1.
    intuition.
    specialize (help2 _ _ _ _ _ _ H6 H4 hz2 H12 h4); intros hz4.
    specialize (eval_expr_with_checks_fixed0 _ _ _ _ _ _ _ _ _ H hz3 h3 hz4 H5 hz1 H3); intros hz5.
    specialize (IHh1 _ _ _ _ _ h2 h3 h4 H6 hz2 H4).
    eapply eval_While_Loop_True1; assumption.
  - (* Swhile *)
    specialize (ast_nums_lt_trans _ _ _ h6 H9); intros hz1.
    specialize (lt_trans_expr _ _ _ _ _ H5 hz1 H3 H12); intros hz2.
    assert (hz3: max1 + 1 <= n).
    specialize (ast_num_bound_stmt _ _ H4); intros ha1.
    intuition.
    specialize (help2 _ _ _ _ _ _ H6 H4 hz2 H12 h4); intros hz4.
    specialize (eval_expr_with_checks_fixed0 _ _ _ _ _ _ _ _ _ H hz3 h3 hz4 H5 hz1 H3); intros hz5.
    specialize (IHh1_1 _ _ _ _ _ h2 h3 h4 H6 hz2 H4).
    simpl in IHh1_2.
    specialize (IHh1_2 _ _ _ _ _ h2 h3 h4 h5 h6 h7).
    eapply eval_While_Loop_True2; auto.
    apply IHh1_1.
    apply IHh1_2.
  - (* Swhile: false branch *)
    specialize (ast_nums_lt_trans _ _ _ h6 H9); intros hz1.
    specialize (lt_trans_expr _ _ _ _ _ H5 hz1 H3 H12); intros hz2.
    assert (hz3: max1 + 1 <= n).
    specialize (ast_num_bound_stmt _ _ H4); intros ha1.
    intuition.
    specialize (help2 _ _ _ _ _ _ H6 H4 hz2 H12 h4); intros hz4.
    specialize (eval_expr_with_checks_fixed0 _ _ _ _ _ _ _ _ _ H hz3 h3 hz4 H5 hz1 H3); intros hz5.
    eapply eval_While_Loop_False; assumption.
Qed.


(**
    for any statement c, generate its checks according to the checking rules and
    the results are stored in cks1, if cks1 is a subset of cks, then,
    whenever executing c from state s0 to s1 under the checks cks1, c can also be executed from
    state s0 to s1 under the checks cks';
    term " subset (max + 1) cks1 cks' " means that: check list cks1 is a subset of check list cks' 
    with respect to the index less than (max + 1), where max is the maximum ast number used
    in statement c;
*)
Lemma eval_stmt_with_checks_fixed: forall cks1 s0 c s1 cks cks0 max,
    eval_stmt_with_checks cks1 s0 c s1 ->
    subset (max + 1) cks1 cks ->
    check_generator_stmt cks0 c cks1 ->
    ast_nums_lt cks0 (get_ast_num_stmt c) ->
    ast_num_inc_stmt c max ->  
    eval_stmt_with_checks cks s0 c s1.
Proof.
    intros.
    apply eval_stmt_with_checks_fixed0 with (cks := cks1) (n := max + 1) (cks1 := cks1) (cks0 := cks0) (max := max); 
    auto.
    apply subset_refl.
Qed.


Lemma eval_decl_with_checks_fixed: forall cks1 s0 d s1 cks cks0 max,
    eval_decl_with_checks cks1 s0 d s1 ->
    subset (max + 1) cks1 cks ->
    check_generator_decl cks0 d cks1 ->
    ast_nums_lt cks0 d.(declaration_astnum) ->
    ast_num_inc_decl d max ->  
    eval_decl_with_checks cks s0 d s1.
Proof.
    intros cks1 s0 d s1 cks cks0 max h1.
    revert cks cks0 max.
    induction h1;
    intros cks cks0 max h2 h3 h4 h5.
  - econstructor; auto.
  - econstructor.
    apply H. 
    inversion h3; subst;
    rewrite <- H in H1; inversion H1; subst.
    inversion h5; subst;
    rewrite <- H in H4; inversion H4; subst.
    specialize (ast_nums_lt_trans _ _ _ h4 H7); intros hz1.
    specialize (eval_expr_with_checks_fixed _ _ _ _ _ _ _ H0 h2 H2 hz1 H5); auto.
  - econstructor; auto.
    apply H0.
    inversion h3; subst;
    rewrite <- H0 in H2; inversion H2; subst.
    inversion h5; subst;
    rewrite <- H0 in H4; inversion H4; subst.
    specialize (ast_nums_lt_trans _ _ _ h4 H7); intros hz1.
    specialize (eval_expr_with_checks_fixed _ _ _ _ _ _ _ H1 h2 H3 hz1 H5); auto.
Qed. 
    
Lemma decl_exists_id: forall d, 
    exists x, x = object_name d.
Proof.
    intros. destruct d; simpl. 
    exists object_name; auto.
Qed.

Lemma eval_decls_with_checks_fixed: forall tl cks1 s0 d s1 cks cks0 max,
    eval_decls_with_checks cks1 s0 (d :: tl) s1 ->
    subset (max + 1) cks1 cks ->
    check_generator_decls cks0 (d :: tl) cks1 ->
    ast_nums_lt cks0 d.(declaration_astnum) ->
    ast_num_inc_decls (d :: tl) max ->  
    eval_decls_with_checks cks s0 (d :: tl) s1.
Proof.
    induction tl;
    intros cks1 s0 d s1 cks cks0 max h1 h2 h3 h4 h5.
  - inversion h3; subst.
    inversion H4; subst.
    inversion h5; subst.
    inversion h1; subst.
    + econstructor.
       specialize (eval_decl_with_checks_fixed _ _ _ _ _ _ _ H6 h2 H2 h4 H0).
       auto.
    + inversion H7; subst.
       specialize (eval_decl_with_checks_fixed _ _ _ _ _ _ _ H5 h2 H2 h4 H0); intros hz1.
       econstructor.
       apply hz1.
       constructor.
  - inversion h3; subst.
    inversion H4; subst.
    inversion h5; subst.

    assert (hz1: n1 + 1 <= n1 + 1); intuition.
    assert (hz2: subset (n1+1) cks1 cks).
      specialize (ast_num_bound_decls _ _ _ H9); intros ha1;
      assert (ha2: n1 + 1 < max + 1); intuition;
      specialize (subset_close _ _ _ _ h2 ha2); auto.
    assert (hz3: subset (n1 + 1) ls'0 cks1). 
      specialize (lt_trans_decl _ _ _ _ _ H2 h4 H5 H8); intros ha1.
      specialize (subset_decls _ _ _ _ _ H4 ha1 H9); intros ha2.
      assert (ha3: n1 + 1 <= declaration_astnum a); intuition.
      specialize (subset_close_le _ _ _ _ ha2 ha3); auto.

    inversion h1; subst.
    + econstructor.
       inversion H10; subst.

       inversion H5; subst;
       rewrite <- H in H7; inversion H7; subst.
       inversion H2; subst;
       rewrite <- H in H1; inversion H1; subst.
       specialize (ast_nums_lt_trans _ _ _ h4 H13); intros hz4.
       specialize (eval_expr_with_checks_fixed0 _ _ _ _ _ _ _ _ _ H0 hz1 hz2 hz3 H12 hz4 H11); intros hz5.
       specialize (decl_exists_id d); intros hz6.
       destruct hz6.
       econstructor. apply H. assumption. 
    + specialize (lt_trans_decl _ _ _ _ _ H2 h4 H5 H8); intros hz4.
       specialize (IHtl _ _ _ _ _ _ _ H11 h2 H4 hz4 H9).
       inversion H5; subst;
       inversion H2; subst;
       inversion H7; subst;
       try match goal with
       | [h1: Some ?i = initialization_expression ?d, h2: None = initialization_expression ?d |- _] => rewrite <- h1 in h2; inversion h2
       end.
       * rewrite <- H in H15; inversion H15; subst. rewrite <- H in H0; inversion H0; subst.
         specialize (decl_exists_id d); intros hz5. destruct hz5.
         econstructor.
         eapply eval_Decl2.
         apply H13. apply H.
         specialize (ast_nums_lt_trans _ _ _ h4 H12); intros hz6.
         specialize (eval_expr_with_checks_fixed0 _ _ _ _ _ _ _ _ _ H18 hz1 hz2 hz3 H10 hz6 H1); intros hz7.
         apply hz7.
         rewrite H13; assumption.
      * specialize (decl_exists_id d); intros hz5. destruct hz5. 
        econstructor.
        eapply eval_Decl0.
        apply H1. assumption. 
        rewrite H1; assumption.
Qed.

(** ** eval_expr_with_checks_complete *)
(**  
    this lemma is used to prove the theorem: well_formed_stmt:
    it means that for any expression e, if it can be evaluated to value v under state s, and cks1 
    is the check list generated for e according to the checking rules, then e should be evaluated
    to the same value v under the check list cks1 in eval_expr_with_checks semantics;
*)

Lemma eval_expr_with_checks_complete: forall s e v cks0 cks1 max,
    eval_expr s e v ->
    check_generator_expr cks0 e cks1 ->
    ast_nums_lt cks0 (get_ast_num_expr e) ->
    ast_num_inc_expr e max ->
    eval_expr_with_checks cks1 s e v.
Proof.
    intros s e v cks0 cks1 max h1.
    revert cks0 cks1 max.
    induction h1;
    intros cks0 cks1 max h2 h3 h4;
    simpl in h3;
    inversion h4; subst.
  - (* Econst *)
    constructor; reflexivity.
  - (* Evar *)
    constructor; auto.
  - (* Ebinop: e1 run time error *)
    specialize (ast_nums_lt_trans _ _ _ h3 H8); intros hz1.
    inversion h2; subst.
    + specialize (lt_trans_expr _ _ _ _ _ H11 hz1 H3 H10); intros hz2.
       specialize (IHh1 _ _ _ H11 hz1 H3).
       specialize (subset_refl (max + 1) cks1); intros hz3.
       specialize (help1 _ _ _ _ _ _ H12 H4 hz2 H10 hz3); intros hz4.
       specialize (eval_expr_with_checks_fixed _ _ _ _ _ _ _ IHh1 hz4 H11 hz1 H3); intros hz5.
       constructor; assumption.
    + specialize (ast_nums_lt_add _ _ _ cks H8 hz1); intros hz2.
       specialize (lt_trans_expr _ _ _ _ _ H12 hz2 H3 H10); intros hz3.
       specialize (IHh1 _ _ _ H12 hz2 H3).
       specialize (subset_refl (max + 1) cks1); intros hz4.
       specialize (help1 _ _ _ _ _ _ H13 H4 hz3 H10 hz4); intros hz5.
       specialize (eval_expr_with_checks_fixed _ _ _ _ _ _ _ IHh1 hz5 H12 hz2 H3); intros hz6.
       constructor; assumption.
  - (* Ebinop: e2 run time error *)
    specialize (ast_nums_lt_trans _ _ _ h3 H8); intros hz1.
    inversion h2; subst.
    + specialize (lt_trans_expr _ _ _ _ _ H11 hz1 H3 H10); intros hz2.
       specialize (IHh1_1 _ _ _ H11 hz1 H3).
       specialize (IHh1_2 _ _ _ H12 hz2 H4).
       specialize (subset_refl (max + 1) cks1); intros hz3.
       specialize (help1 _ _ _ _ _ _ H12 H4 hz2 H10 hz3); intros hz4.
       specialize (eval_expr_with_checks_fixed _ _ _ _ _ _ _ IHh1_1 hz4 H11 hz1 H3); intros hz5.
       eapply eval_Binary_Operation2.
       * apply hz5.
       * assumption.
    + specialize (ast_nums_lt_add _ _ _ cks H8 hz1); intros hz2.
       specialize (lt_trans_expr _ _ _ _ _ H12 hz2 H3 H10); intros hz3.
       specialize (IHh1_1 _ _ _ H12 hz2 H3).
       specialize (IHh1_2 _ _ _ H13 hz3 H4).
       specialize (subset_refl (max + 1) cks1); intros hz4.
       specialize (help1 _ _ _ _ _ _ H13 H4 hz3 H10 hz4); intros hz5.
       specialize (eval_expr_with_checks_fixed _ _ _ _ _ _ _ IHh1_1 hz5 H12 hz2 H3); intros hz6.
       eapply eval_Binary_Operation2. 
       * apply hz6.
       * assumption.
  - (* Ebinop: run time error on binary operation *)
    specialize (ast_nums_lt_trans _ _ _ h3 H9); intros hz1.
    inversion h2; subst.
    + destruct op; inversion H; subst;
       inversion H8; subst;
       intuition.
    + assert(ha: fetch_cks ast_num cks1 = cks).
        replace ast_num with (get_ast_num_expr (E_Binary_Operation ast_num op e1 e2)).
        apply fetch_cks_inv with (cks0 := cks0) (max := max); auto.
        auto.      
      specialize (ast_nums_lt_add _ _ _ cks H9 hz1); intros hz2.
      specialize (lt_trans_expr _ _ _ _ _ H13 hz2 H4 H11); intros hz3.
      specialize (IHh1_1 _ _ _ H13 hz2 H4).
      specialize (IHh1_2 _ _ _ H14 hz3 H5).
      specialize (subset_refl (max + 1) cks1); intros hz4.
      specialize (help1 _ _ _ _ _ _ H14 H5 hz3 H11 hz4); intros hz5.
      specialize (eval_expr_with_checks_fixed _ _ _ _ _ _ _ IHh1_1 hz5 H13 hz2 H4); intros hz6.
      eapply eval_Binary_Operation3. 
       * apply hz6.
       * apply IHh1_2.
       * apply ha.
       * specialize (do_complete_checks_correct' _ _ _ _ _ _ _ _ H7 H); auto.
  - (* Ebinop: normal value *)
    specialize (ast_nums_lt_trans _ _ _ h3 H10); intros hz1.
    inversion h2; subst.
    + assert(ha: fetch_cks ast_num cks1 = nil).
        replace ast_num with (get_ast_num_expr (E_Binary_Operation ast_num op e1 e2)).
        apply fetch_cks_inv with (cks0 := cks0) (max := max); auto.
        auto.
      specialize (lt_trans_expr _ _ _ _ _ H13 hz1 H5 H12); intros hz2.
       specialize (IHh1_1 _ _ _ H13 hz1 H5).
       specialize (IHh1_2 _ _ _ H14 hz2 H6).
       specialize (subset_refl (max + 1) cks1); intros hz3.
       specialize (help1 _ _ _ _ _ _ H14 H6 hz2 H12 hz3); intros hz4.
       specialize (eval_expr_with_checks_fixed _ _ _ _ _ _ _ IHh1_1 hz4 H13 hz1 H5); intros hz5.
       eapply eval_Binary_Operation4.
       * apply hz5.
       * apply IHh1_2.
       * apply ha.
       * constructor.
       * assumption.
    + assert(ha: fetch_cks ast_num cks1 = cks).
        replace ast_num with (get_ast_num_expr (E_Binary_Operation ast_num op e1 e2)).
        apply fetch_cks_inv with (cks0 := cks0) (max := max); auto.
        auto.
      specialize (ast_nums_lt_add _ _ _ cks H10 hz1); intros hz2.
       specialize (lt_trans_expr _ _ _ _ _ H14 hz2 H5 H12); intros hz3.
       specialize (IHh1_1 _ _ _ H14 hz2 H5).
       specialize (IHh1_2 _ _ _ H15 hz3 H6).
       specialize (subset_refl (max + 1) cks1); intros hz4.
       specialize (help1 _ _ _ _ _ _ H15 H6 hz3 H12 hz4); intros hz5.
       specialize (eval_expr_with_checks_fixed _ _ _ _ _ _ _ IHh1_1 hz5 H14 hz2 H5); intros hz6.
       eapply eval_Binary_Operation4. 
       * apply hz6.
       * apply IHh1_2.
       * apply ha.
       * specialize (do_complete_checks_correct' _ _ _ _ _ _ _ _ H8 H); auto.
       * assumption.
  - (* Eunop: exception *)
    specialize (ast_nums_lt_trans _ _ _ h3 H4); intros hz1.
    inversion h2; subst.
    + specialize (IHh1 _ _ _ H5 hz1 H1).
       constructor. 
       assumption.
  - (* Eunop: normal value *)
    specialize (ast_nums_lt_trans _ _ _ h3 H5); intros hz1.
    inversion h2; subst.
    + specialize (IHh1 _ _ _ H6 hz1 H2).
       econstructor.
       apply IHh1.
       assumption.
Qed.


(** 
    Because we cannot prove eval_stmt_with_checks_correct directly, so 
    eval_stmt_with_checks_correct0 is proved as an intermediate proof 
    step by introducing "subset", it's similar to eval_expr_with_checks_correct0;
*)
Theorem eval_stmt_with_checks_correct_0: forall cks s c s' cks1 cks0 max,
    eval_stmt_with_checks cks s c s' ->
    subset (max + 1) cks1 cks ->
    check_generator_stmt cks0 c cks1 ->
    ast_nums_lt cks0 (get_ast_num_stmt c) ->
    ast_num_inc_stmt c max ->
    eval_stmt s c s'.
Proof.
    intros cks s c s' cks1 cks0 max h1.
    generalize cks1 cks0 max.
    clear cks1 cks0 max.
    induction h1;
    intros cks1 cks0 max h2 h3 h4 h5;
    simpl in h4; inversion h3; inversion h5; subst.
  - (* Sassign *)
    specialize (ast_nums_lt_trans _ _ _ h4 H12); intros hz1.
    specialize (eval_expr_with_checks_correct0 _ _ _ _ _ _ _ H h2 H5 hz1 H9); intros hz2.
    constructor;
    assumption.
  - specialize (ast_nums_lt_trans _ _ _ h4 H13); intros hz1.
    specialize (eval_expr_with_checks_correct0 _ _ _ _ _ _ _ H h2 H6 hz1 H10); intros hz2.
    econstructor.
    apply hz2.
    assumption.
  - (* Sseq *)
    specialize (ast_nums_lt_trans _ _ _ h4 H13); intros hz1.
    specialize (lt_trans_stmt _ _ _ _ _ H4 hz1 H9 H16); intros hz2.
    specialize (help2 _ _ _ _ _ _ H5 H10 hz2 H16 h2); intros hz3.
    specialize (IHh1 _ _ _ hz3 H4 hz1 H9).
    constructor; assumption.
  - specialize (ast_nums_lt_trans _ _ _ h4 H13); intros hz1.
    specialize (lt_trans_stmt _ _ _ _ _ H4 hz1 H9 H16); intros hz2.
    specialize (help2 _ _ _ _ _ _ H5 H10 hz2 H16 h2); intros hz3.
    specialize (IHh1_1 _ _ _ hz3 H4 hz1 H9).
    specialize (IHh1_2 _ _ _ h2 H5 hz2 H10).
    econstructor.
    apply IHh1_1.
    assumption.
  - (* Sifthen *)
    specialize (ast_nums_lt_trans _ _ _ h4 H14); intros hz1.
    specialize (lt_trans_expr _ _ _ _ _ H5 hz1 H10 H17); intros hz2.
    specialize (help2 _ _ _ _ _ _ H6 H11 hz2 H17 h2); intros hz3.
    specialize (eval_expr_with_checks_correct0 _ _ _ _ _ _ _ H hz3 H5 hz1 H10); intros hz4.
    constructor; 
    assumption.
  - specialize (ast_nums_lt_trans _ _ _ h4 H14); intros hz1.
    specialize (lt_trans_expr _ _ _ _ _ H5 hz1 H10 H17); intros hz2.
    specialize (help2 _ _ _ _ _ _ H6 H11 hz2 H17 h2); intros hz3.
    specialize (eval_expr_with_checks_correct0 _ _ _ _ _ _ _ H hz3 H5 hz1 H10); intros hz4.
    specialize (IHh1 _ _ _ h2 H6 hz2 H11).
    econstructor; try assumption. 
  - specialize (ast_nums_lt_trans _ _ _ h4 H14); intros hz1.
    specialize (lt_trans_expr _ _ _ _ _ H5 hz1 H10 H17); intros hz2.
    specialize (help2 _ _ _ _ _ _ H6 H11 hz2 H17 h2); intros hz3.
    specialize (eval_expr_with_checks_correct0 _ _ _ _ _ _ _ H hz3 H5 hz1 H10); intros hz4.
    apply eval_S_If_False; assumption.
  - (* Swhile *)
    specialize (ast_nums_lt_trans _ _ _ h4 H14); intros hz1.
    specialize (lt_trans_expr _ _ _ _ _ H5 hz1 H10 H17); intros hz2.
    specialize (help2 _ _ _ _ _ _ H6 H11 hz2 H17 h2); intros hz3.
    specialize (eval_expr_with_checks_correct0 _ _ _ _ _ _ _ H hz3 H5 hz1 H10); intros hz4.
    constructor; 
    assumption.   
  - specialize (ast_nums_lt_trans _ _ _ h4 H14); intros hz1.
    specialize (lt_trans_expr _ _ _ _ _ H5 hz1 H10 H17); intros hz2.
    specialize (help2 _ _ _ _ _ _ H6 H11 hz2 H17 h2); intros hz3.
    specialize (eval_expr_with_checks_correct0 _ _ _ _ _ _ _ H hz3 H5 hz1 H10); intros hz4.
    specialize (IHh1 _ _ _ h2 H6 hz2 H11).
    eapply eval_S_While_Loop_True1; try assumption.
  - specialize (ast_nums_lt_trans _ _ _ h4 H14); intros hz1.
    specialize (lt_trans_expr _ _ _ _ _ H5 hz1 H10 H17); intros hz2.
    specialize (help2 _ _ _ _ _ _ H6 H11 hz2 H17 h2); intros hz3.
    specialize (eval_expr_with_checks_correct0 _ _ _ _ _ _ _ H hz3 H5 hz1 H10); intros hz4.
    specialize (IHh1_1 _ _ _ h2 H6 hz2 H11).
    specialize (IHh1_2 _ _ _ h2 h3 h4 h5).
    eapply eval_S_While_Loop_True2; auto.
    apply IHh1_1. apply IHh1_2.
  - specialize (ast_nums_lt_trans _ _ _ h4 H14); intros hz1.
    specialize (lt_trans_expr _ _ _ _ _ H5 hz1 H10 H17); intros hz2.
    specialize (help2 _ _ _ _ _ _ H6 H11 hz2 H17 h2); intros hz3.
    specialize (eval_expr_with_checks_correct0 _ _ _ _ _ _ _ H hz3 H5 hz1 H10); intros hz4.
    eapply eval_S_While_Loop_False; auto.
Qed.

(** ** eval_stmt_with_checks_correct *)
(**
    cks is checks that are generated for statement c according to 
    the checking rules built on top of cks0, then whenever c is 
    evaluated to a state s' under checks cks, statement c can also 
    be evaluated to state s' in relational semantics eval_stmt;
    ast_num_inc_stmt is used to constrain that all ast numbers used 
    in c are unique and increasing;
    ast_nums_lt is used to enforce that new checks added for c will 
    not overlap the checks cks0 built for previous AST nodes
*)
Theorem eval_stmt_with_checks_correct: forall cks s c s' cks0 max,
    eval_stmt_with_checks cks s c s' ->
    check_generator_stmt cks0 c cks ->
    ast_nums_lt cks0 (get_ast_num_stmt c) ->
    ast_num_inc_stmt c max ->
    eval_stmt s c s'.
Proof.
    intros.
    specialize (subset_refl (max + 1) cks); intros hz1.
    specialize (eval_stmt_with_checks_correct_0 _ _ _ _ _ _ _ H hz1 H0 H1 H2).
    auto.
Qed.

Theorem eval_decl_with_checks_correct0: forall cks s d s' cks1 cks0 max,
    eval_decl_with_checks cks s d s' ->
    subset (max + 1) cks1 cks ->
    check_generator_decl cks0 d cks1 ->
    ast_nums_lt cks0 d.(declaration_astnum) ->
    ast_num_inc_decl d max ->
    eval_decl s d s'.
Proof.
    intros cks s d s' cks1 cks0 max h1.
    revert cks1 cks0 max.
    induction h1;
    intros cks1 cks0 max h2 h3 h4 h5.
  - constructor; assumption.
  - econstructor.
    apply H.
    inversion h3; subst;
    rewrite <- H in H1; inversion H1; subst.
    inversion h5; subst;
    rewrite <- H in H4; inversion H4; subst.
    specialize (ast_nums_lt_trans _ _ _ h4 H7); intros hz1.
    specialize (eval_expr_with_checks_correct0 _ _ _ _ _ _ _ H0 h2 H2 hz1 H5).
    auto.
  - econstructor; auto.
    apply H0.
    inversion h3; subst;
    rewrite <- H0 in H2; inversion H2; subst.
    inversion h5; subst;
    rewrite <- H0 in H4; inversion H4; subst.
    specialize (ast_nums_lt_trans _ _ _ h4 H7); intros hz1.
    specialize (eval_expr_with_checks_correct0 _ _ _ _ _ _ _ H1 h2 H3 hz1 H5);
    auto.
Qed.


Theorem eval_decl_with_checks_correct: forall cks s d s' cks0 max,
    eval_decl_with_checks cks s d s' ->
    check_generator_decl cks0 d cks ->
    ast_nums_lt cks0 d.(declaration_astnum) ->
    ast_num_inc_decl d max ->
    eval_decl s d s'.
Proof.
    intros.
    specialize (subset_refl (max + 1) cks); intros hz1.
    specialize (eval_decl_with_checks_correct0 _ _ _ _ _ _ _ H hz1 H0 H1 H2).
    auto.
Qed.

Theorem eval_decls_with_checks_correct0: forall tl cks s d s' cks1 cks0 max,
    eval_decls_with_checks cks s (d :: tl) s' ->
    subset (max + 1) cks1 cks ->
    check_generator_decls cks0 (d :: tl) cks1 ->
    ast_nums_lt cks0 d.(declaration_astnum) ->
    ast_num_inc_decls (d :: tl) max ->
    eval_decls s (d :: tl) s'.
Proof.
    induction tl;
    intros.
  - inversion H1; subst.
    inversion H9; subst.
    inversion H3; subst.
    inversion H; subst.
    + specialize (eval_decl_with_checks_correct0 _ _ _ _ _ _ _ H11 H0 H7 H2 H5); intros hz1.
       constructor; auto.
    + inversion H12; subst.
       specialize (eval_decl_with_checks_correct0 _ _ _ _ _ _ _ H10 H0 H7 H2 H5); intros hz1.
       econstructor.
       apply hz1. constructor.
  - inversion H1; subst.
    inversion H3; subst.

    specialize (lt_trans_decl _ _ _ _ _ H7 H2 H8 H11); intros hz1.
    assert (hz2: subset (n1 + 1) ls'0 cks). 
      specialize (subset_decls _ _ _ _ _ H9 hz1 H12); intros ha1.
      specialize (ast_num_bound_decls _ _ _ H12); intros ha2.
      assert (ha3: declaration_astnum a < max + 1); intuition.
      specialize (subset_trans _ _ _ _ _ ha1 H0 ha3); intros ha4.
      assert (ha5: n1 + 1 <= declaration_astnum a); intuition.
      specialize(subset_close_le _ _ _ _ ha4 ha5); auto.

    inversion H; subst.
    + specialize (eval_decl_with_checks_correct0 _ _ _ _ _ _ _ H13 hz2 H7 H2 H8); intros hz3.
       constructor; auto.
    + specialize (IHtl _ _ _ _ _ _ _ H14 H0 H9 hz1 H12).
       specialize (eval_decl_with_checks_correct0 _ _ _ _ _ _ _ H10 hz2 H7 H2 H8); intros hz3.
       econstructor.
       apply hz3. assumption.
Qed.


(** for declaration part with a least one declaration statement; *)
Theorem eval_decls_with_checks_correct: forall tl cks s d s' cks0 max,
    eval_decls_with_checks cks s (d :: tl) s' ->
    check_generator_decls cks0 (d :: tl) cks ->
    ast_nums_lt cks0 d.(declaration_astnum) ->
    ast_num_inc_decls (d :: tl) max ->
    eval_decls s (d :: tl) s'.
Proof.
    intros.
    specialize (subset_refl (max + 1) cks); intros hz1.
    specialize (eval_decls_with_checks_correct0 _ _ _ _ _ _ _ _ H hz1 H0 H1 H2).
    auto.
Qed.


Lemma eval_proc_body_with_checks_correct0: forall cks s f s' cks1 cks0 max,
    eval_proc_body_with_checks cks s f s' ->
    subset (max + 1) cks1 cks ->
    check_generator_proc_body cks0 f cks1 ->
    ast_nums_lt cks0 f.(procedure_astnum) ->
    ast_num_inc_proc_body f max ->
    eval_proc s f s'.
Proof.
    intros cks s f s' cks1 cks0 max h1.
    revert cks1 cks0 max.
    induction h1; subst;
    intros cks1 cks0 max h2 h3 h4 h5;
    inversion h3; subst.
  - remember (procedure_declarative_part f) as x.
    destruct x.
    + inversion H.
    + econstructor.
       rewrite <- Heqx.
       inversion h5; subst;
       rewrite <- Heqx in H2; inversion H2; subst.
       rewrite <- Heqx in H3.
       specialize (ast_nums_lt_trans _ _ _ h4 H5); intros hz1.
       assert (hz2: ast_nums_lt ls2 (get_ast_num_stmt (procedure_statements f))). 
         specialize (lt_trans_decls _ _ _ _ _ _ H0 hz1 H3 H7); auto.
       assert (hz3: subset (max1 + 1) ls2 cks). 
         specialize (subset_stmt _ _ _ _ H1 hz2 H4); intros ha1.
         assert (ha2: get_ast_num_stmt (procedure_statements f) < max + 1).
         specialize (ast_num_bound_stmt _ _ H4); intros ha2. intuition.
         assert (ha3: max1 + 1 <= get_ast_num_stmt (procedure_statements f)); intuition.
         specialize (subset_trans _ _ _ _ _ ha1 h2 ha2); intros ha4.
         specialize (subset_close_le _ _ _ _ ha4 ha3); auto.
       specialize (ast_nums_lt_trans _ _ _ h4 H5); intros hz4.
       specialize (eval_decls_with_checks_correct0 _ _ _ _ _ _ _ _ H hz3 H0 hz4 H3).
       auto.
  - inversion h5; subst;
    rewrite <- H3 in *.
    + inversion H; subst.
      inversion H1; subst.
      assert (hz1 : ast_nums_lt ls2 (get_ast_num_stmt (procedure_statements f))).
        specialize (ast_nums_lt_trans _ _ _ h4 H5); auto.
      specialize (eval_stmt_with_checks_correct_0 _ _ _ _ _ _ _ H0 h2 H2 hz1 H4); intros hz2.
      econstructor. rewrite <- H3. 
      assert (hz3: eval_decls s'0 nil (S_Normal s'0)); constructor.
      assumption.
    + specialize (ast_nums_lt_trans _ _ _ h4 H6); intros hz1.
      assert (hz2: ast_nums_lt ls2 (get_ast_num_stmt (procedure_statements f))).
        specialize (lt_trans_decls _ _ _ _ _ _ H1 hz1 H4 H8); auto.
      assert (hz3: subset (max1 + 1) ls2 cks). 
        specialize (subset_stmt _ _ _ _ H2 hz2 H5); intros ha1.
        assert (ha2: get_ast_num_stmt (procedure_statements f) < max + 1).
        specialize (ast_num_bound_stmt _ _ H5); intros ha2. intuition.
        assert (ha3: max1 + 1 <= get_ast_num_stmt (procedure_statements f)); intuition.
        specialize (subset_trans _ _ _ _ _ ha1 h2 ha2); intros ha4.
        specialize (subset_close_le _ _ _ _ ha4 ha3); auto.
      specialize (ast_nums_lt_trans _ _ _ h4 H6); intros hz4.
      specialize (eval_decls_with_checks_correct0 _ _ _ _ _ _ _ _ H hz3 H1 hz4 H4); intros hz5.
      specialize (eval_stmt_with_checks_correct_0 _ _ _ _ _ _ _ H0 h2 H2 hz2 H5); intros hz6.
      econstructor.
      rewrite <- H3. apply hz5. assumption.
Qed.

Theorem eval_proc_body_with_checks_correct: forall cks1 s f s' cks0 max,
    eval_proc_body_with_checks cks1 s f s' ->
    check_generator_proc_body cks0 f cks1 ->
    ast_nums_lt cks0 f.(procedure_astnum) ->
    ast_num_inc_proc_body f max ->
    eval_proc s f s'.
Proof.
    intros.
    specialize (subset_refl (max + 1) cks1); intros hz1.
    specialize (eval_proc_body_with_checks_correct0 _ _ _ _ _ _ _ H hz1 H0 H1 H2).
    auto.
Qed.


Lemma eval_subprogram_with_checks_correct0: forall cks s ast_num f s' cks1 cks0 max,
    eval_subprogram_with_checks cks s (Procedure ast_num f) s' ->
    subset (max + 1) cks1 cks ->
    check_generator_subprogram cks0 (Procedure ast_num f) cks1 ->
    ast_nums_lt cks0 ast_num ->
    ast_num_inc_subprogram (Procedure ast_num f) max ->
    eval_subprogram s (Procedure ast_num f) s'.
Proof.
    intros.
    inversion H; subst.
    inversion H1; subst.
    inversion H3; subst.
    specialize (ast_nums_lt_trans _ _ _ H2 H6); intros hz1.
    specialize (eval_proc_body_with_checks_correct0 _ _ _ _ _ _ _ H8 H0 H9 hz1 H10);
    intros hz2.
    constructor.
    assumption.
Qed.

Lemma eval_subprogram_with_checks_correct: forall cks1 s ast_num f s' cks0 max,
    eval_subprogram_with_checks cks1 s (Procedure ast_num f) s' ->
    check_generator_subprogram cks0 (Procedure ast_num f) cks1 ->
    ast_nums_lt cks0 ast_num ->
    ast_num_inc_subprogram (Procedure ast_num f) max ->
    eval_subprogram s (Procedure ast_num f) s'.
Proof.
    intros.
    specialize (subset_refl (max + 1) cks1); intros hz1.
    specialize (eval_subprogram_with_checks_correct0 _ _ _ _ _ _ _ _ H hz1 H0 H1 H2).
    auto.
Qed.


(************************************************************************************************)
(*   Prove that well-formed expression can evaluate to either normal value or some exception    *)
(************************************************************************************************)

(**
    expressions (or statements) accompanied with correct run time 
    checks, which are produced according to the checking rules, are 
    called well-checked expressions (or statements);
*)
Definition well_checked_expr := check_generator_expr.

Definition well_checked_stmt := check_generator_stmt.

Definition well_checked_decl := check_generator_decl.

Definition well_checked_decls := check_generator_decls.

Definition well_checked_proc_body := check_generator_proc_body.

Definition well_checked_subprogram := check_generator_subprogram.

(**
    for any well-typed, well-defined (all used variables have benn 
    initialized) and well-checked (with right checks put at the right 
    places according to checking rules) expression e, it can always 
    be evaluated to a value v under the eval_expr_with_checks semantics, 
    where v can be either a normal value or a run time error;
*)
Lemma well_formed_expr0: forall tb s m e t cks0 cks1 max,
    type_check_store tb s -> 
    mode_mapping tb s m -> (* m: a map from variable to its initialization state and in/out mode *)
    well_defined_expr m e ->
    well_typed_expr tb e t ->
    well_checked_expr cks0 e cks1 ->
    ast_nums_lt cks0 (get_ast_num_expr e) ->
    ast_num_inc_expr e max ->
    exists v, eval_expr_with_checks cks1 s e v.
Proof.
    intros tb s m e t cks0 cks1 max h1 h2 h3.
    revert t cks0 cks1 max. 
    induction h3;
    intros t cks0 cks1 max h4 h5 h6 h7.
  - (* 1. Econst_Int *)
    exists (Val_Normal (Int n)).
    constructor. 
    simpl; auto.
  - (* 2. Econst_Bool *)
    exists (Val_Normal (Bool b)).
    constructor.
    simpl; auto.
  - (* 3. Evar *)
    specialize (fetch_exists _ _ _ _ _ h2 H); intros hz1;
    destruct hz1;
    exists (Val_Normal x0);
    constructor; assumption.
  - (* 4. Ebinop *)
    simpl in h6;
    inversion h4; subst;
    inversion h5; subst;
    inversion h7; subst.
    { assert (ha: fetch_cks ast_num cks1 = nil).
        replace ast_num with (get_ast_num_expr (E_Binary_Operation ast_num op e1 e2)).
        apply fetch_cks_inv with (cks0 := cks0) (max := max); auto.
        auto.
      specialize (ast_nums_lt_trans _ _ _ h6 H14); intros hz1.
      specialize (IHh3_1 h2 _ _ _ _ H5 H9 hz1 H3).
      specialize (lt_trans_expr _ _ _ _ _ H9 hz1 H3 H16); intros hz2.
      specialize (IHh3_2 h2 _ _ _ _ H6 H10 hz2 H4).
      rm_exists.
      assert (ha1: eval_expr_with_checks cks1 s e1 x0).
        specialize (subset_expr _ _ _ _ H10 hz2 H4); intros hz3.
        assert (hz4: max1 + 1 <= get_ast_num_expr e2). intuition.
        specialize (subset_close_le _ _ _ _ hz3 hz4); intros hz5.
        specialize (eval_expr_with_checks_fixed _ _ _ _ _ _ _ H0 hz5 H9 hz1 H3); auto.
      specialize (eval_expr_with_checks_state _ _ _ _ H0); intros hz3;
      specialize (eval_expr_with_checks_state _ _ _ _ H); intros hz4.
      inversion hz3; clear hz3; inversion hz4; clear hz4;
      rm_exists; subst.
      + specialize (eval_type_reserve2 _ _ _ _ _ _ h1 ha1 H5); intros hz3.
        specialize (eval_type_reserve2 _ _ _ _ _ _ h1 H H6); intros hz4.
        destruct x1, x2;
        inversion hz3; subst; inversion hz4; subst.
        - exists (f_eval_bin_expr op (Int n0) (Int n)).
          destruct op; inversion H7; simpl;
          match goal with
          | _ => 
              eapply eval_Binary_Operation4;
              [apply ha1 | apply H | apply ha | constructor | constructor; auto]
          end.
        - exists (f_eval_bin_expr op (Bool b0) (Bool b)).
          destruct op; inversion H7; simpl;
          match goal with
          | _ => 
              eapply eval_Binary_Operation4;
              [apply ha1 | apply H | apply ha | constructor | constructor; auto]
          end.
      + exists Val_Run_Time_Error.
        eapply eval_Binary_Operation2.
        apply ha1.
        assumption.
      + exists Val_Run_Time_Error.
        eapply eval_Binary_Operation1.
        apply ha1.
      + exists Val_Run_Time_Error.
        eapply eval_Binary_Operation1.
        apply ha1.
    }
    { specialize (ast_nums_lt_trans _ _ _ h6 H15); intros hz1.
      specialize (ast_nums_lt_add _ _ _ cks H15 hz1); intros hz2.
      specialize (IHh3_1 h2 _ _ _ _ H5 H10 hz2 H3).
      specialize (lt_trans_expr _ _ _ _ _ H10 hz2 H3 H17); intros hz3.
      specialize (IHh3_2 h2 _ _ _ _ H6 H11 hz3 H8).
      rm_exists.
      assert (ha1: eval_expr_with_checks cks1 s e1 x0).
        specialize (subset_expr _ _ _ _ H11 hz3 H8); intros hz4.
        assert (hz5: max1 + 1 <= get_ast_num_expr e2); intuition.
        specialize (subset_close_le _ _ _ _ hz4 hz5); intros hz6.
        specialize (eval_expr_with_checks_fixed _ _ _ _ _ _ _ H0 hz6 H10 hz2 H3); auto.
      specialize (eval_expr_with_checks_state _ _ _ _ H0); intros hz4;
      specialize (eval_expr_with_checks_state _ _ _ _ H); intros hz5.
      inversion hz4; clear hz4; inversion hz5; clear hz5;
      rm_exists; subst.
      assert (ha: fetch_cks ast_num cks1 = cks).
        replace ast_num with (get_ast_num_expr (E_Binary_Operation ast_num op e1 e2)).
        apply fetch_cks_inv with (cks0 := cks0) (max := max); auto.
        auto.
      + specialize (eval_type_reserve2 _ _ _ _ _ _ h1 ha1 H5); intros hz4.
        specialize (eval_type_reserve2 _ _ _ _ _ _ h1 H H6); intros hz5.
        destruct x1, x2;
        inversion hz4; subst; inversion hz5; subst.
        - destruct op; inversion H4; subst;
          try match goal with
          | h1: fetch_cks ?ast_num ?cks <> nil, h2: nil = fetch_cks ?ast_num ?cks |- _ =>
              rewrite h2 in h1; rm_false_hyp
          end.
          (* 1. Plus *)
          { remember ((Zge_bool (n0 + n) min_signed) && (Zle_bool (n0 + n) max_signed)) as x.
            symmetry in Heqx.
            destruct x.
            * exists (Val_Normal (Int (n0 + n))).
              eapply eval_Binary_Operation4.
              apply ha1. apply H. symmetry in H14; apply H14.
              repeat constructor; auto.
              constructor; auto.
            * exists Val_Run_Time_Error.
              eapply eval_Binary_Operation3.
              apply ha1. apply H. symmetry in H14; apply H14.
              repeat constructor; auto.
          }
          (* 2. Minus *)
          { remember ((Zge_bool (n0 - n) min_signed) && (Zle_bool (n0 - n) max_signed)) as x.
            symmetry in Heqx.
            destruct x.
            * exists (Val_Normal (Int (n0 - n))).
              eapply eval_Binary_Operation4.
              apply ha1. apply H. symmetry in H14; apply H14.
              repeat constructor; auto.
              constructor; auto.
            * exists Val_Run_Time_Error.
              eapply eval_Binary_Operation3.
              apply ha1. apply H. symmetry in H14; apply H14.
              repeat constructor; auto.
          }
          (* 3. Multiply *)
          { remember ((Zge_bool (n0 * n) min_signed) && (Zle_bool (n0 * n) max_signed)) as x.
            symmetry in Heqx.
            destruct x.
            * exists (Val_Normal (Int (n0 * n))).
              eapply eval_Binary_Operation4.
              apply ha1. apply H. symmetry in H14; apply H14.
              repeat constructor; auto.
              constructor; auto.
            * exists Val_Run_Time_Error.
              eapply eval_Binary_Operation3.
              apply ha1. apply H. symmetry in H14; apply H14.
              repeat constructor; auto.
          }
          (* 4. Divide *)
          { remember ((negb (Zeq_bool n 0)) && ((Zge_bool (Z.quot n0 n) min_signed) && (Zle_bool (Z.quot n0 n) max_signed))) as x.
            symmetry in Heqx.
            destruct x.
            * exists (Val_Normal (Int (Z.quot n0 n))).
              eapply eval_Binary_Operation4.
              apply ha1. apply H. symmetry in H14; apply H14.
              repeat constructor; auto;
              destruct (negb (Zeq_bool n 0)); inversion Heqx; auto.
              constructor; auto.
            * exists Val_Run_Time_Error.
              eapply eval_Binary_Operation3.
              apply ha1. apply H. symmetry in H14; apply H14.
              remember (negb (Zeq_bool n 0)) as y.
              symmetry in Heqy.
              destruct y; simpl in Heqx.
              apply Do_Checks_True;
              repeat constructor; auto.
              repeat constructor; auto.
          }
        - destruct op; inversion H7; simpl;
          inversion H4; subst;
          match goal with
          | h1: fetch_cks ?ast_num ?cks <> nil, h2: nil = fetch_cks ?ast_num ?cks |- _ =>
              rewrite h2 in h1; rm_false_hyp
          end.
      + exists Val_Run_Time_Error.
        eapply eval_Binary_Operation2.
        apply ha1.
        assumption.
      + exists Val_Run_Time_Error.
        eapply eval_Binary_Operation1.
        apply ha1.
      + exists Val_Run_Time_Error.
        eapply eval_Binary_Operation1.
        apply ha1.
    }
  - (* 5. Eunop *)
    inversion h4; subst.
    inversion h5; subst;
    simpl in h6;
    inversion h7; subst;
    specialize (ast_nums_lt_trans _ _ _ h6 H6); intros hz1;
    specialize (IHh3 h2 _ _ _ _ H3 H4 hz1 H1);
    rm_exists.

    specialize (eval_expr_with_checks_state _ _ _ _ H); intros hz2.
    destruct hz2; rm_exists; subst.
    + exists (f_eval_unary_expr op x0).
       specialize (eval_type_reserve2 _ _ _ _ _ _ h1 H H3); intros hz8.
       destruct x0; try rm_contradict.
       destruct op. econstructor.
       apply H. 
       constructor.
       reflexivity.
    + exists Val_Run_Time_Error.
       constructor.
       assumption.
Qed.

(** ** well_formed_expr *)
(**
    the difference with well_formed_expr0 is that their conclusions 
    are different, here the conclusion is the reference semantics 
    for expression e: "eval_expr s e v"; 

    for any well-typed, well-defined (all used variables have benn 
    initialized) and well-checked (with right checks put at the right 
    places according to checking rules) expression e, it can always 
    be evaluated to a value v under the eval_expr reference semantics, 
    where v can be either a normal value or a run time error;
*)
Theorem well_formed_expr: forall tb s m e t cks0 cks1 max,
    type_check_store tb s -> 
    mode_mapping tb s m -> (* m: a map from variable to its initialization state and in/out mode *)
    well_defined_expr m e ->
    well_typed_expr tb e t ->
    well_checked_expr cks0 e cks1 ->
    ast_nums_lt cks0 (get_ast_num_expr e) ->
    ast_num_inc_expr e max ->
    exists v, eval_expr s e v.
Proof.
    intros.
    specialize (well_formed_expr0 _ _ _ _ _ _ _ _ H H0 H1 H2 H3 H4 H5); intros hz1.
    destruct hz1.
    specialize (eval_expr_with_checks_correct _ _ _ _ _ _ H6 H3 H4 H5); intros hz2.
    exists x.
    assumption.
Qed.

(* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - *)

(* some help lemmas *)

Lemma valid_update: forall tb s ast_id x e v,
    type_check_store tb s ->
    well_typed_stmt tb (S_Assignment ast_id x e) ->
    exists s', update s x (Value v) = Some s'.
Proof.
    intros tb s ast_id x e v h1 h2.
    inversion h2; subst.
    specialize (typed_value' _ _ _ m t h1 H2); intros hz1.
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

(** for a well-typed store, any updates to its element x with a value of its expected type should
     should still keep the store well-typed;
*)
Lemma type_reserve_update: forall s x v s' tb m t ,
    update s x (Value v) = Some s' ->    
    type_check_store tb s -> 
    lookup x tb = Some (m, t)-> 
    value_of_type v t ->
    type_check_store tb s'.
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

(** the resulting store should be well-typed after the modification 
    to the initially well-typed store by a well-typed assignment;
*)
Lemma type_reserve_assign: forall tb s ast_id x e v s',
    type_check_store tb s -> 
    well_typed_stmt tb (S_Assignment ast_id x e) -> 
    eval_expr s e (Val_Normal v) ->
    update s x (Value v) = Some s' ->
    type_check_store tb s'. 
Proof.
    intros tb s ast_id x e v s' h1 h2 h3 h4.
    inversion h2; subst.
    specialize (eval_type_reserve _ _ _ _ _ h1 h3 H4); intros hz1.
    specialize (type_reserve_update _ _ _ _ _ _ _ h4 h1 H2 hz1); intros hz2.
    assumption.
Qed.

(** for any s, c and s' satisfying the relation "eval_stmt s c s'",
    the resulting state s' can be either a run time error or 
    a normal state; 
*)
Lemma well_typed_stmt_result: forall tb s c s',
    type_check_store tb s -> 
    well_typed_stmt tb c ->
    eval_stmt s c s' -> 
    s' = S_Run_Time_Error \/ (exists s0, s' = S_Normal s0 /\ type_check_store tb s0).
Proof.
    intros tb s c s' h1 h2 h3.
    induction h3;
    try match goal with
    | [ |- S_Run_Time_Error = S_Run_Time_Error \/ _ ] => left; reflexivity
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

(** if the initial store is well-typed, and when we execute a 
    well-typed statement, the resulting normal store should also 
    be well-typed;
*)
Lemma type_reserve_stmt: forall tb s c s',
    type_check_store tb s -> 
    well_typed_stmt tb c ->
    eval_stmt s c (S_Normal s') -> 
    type_check_store tb s'. 
Proof.
    intros tb s c s' h1 h2 h3.
    remember (S_Normal s') as s1.
    specialize (well_typed_stmt_result _ _ _ _ h1 h2 h3); intros hz1.
    subst.
    destruct hz1 as [hz2 | hz2]; inversion hz2.
    destruct H.
    inversion H; subst.
    assumption.
Qed.

Lemma typed_store_reserve_decl: forall tb s d tb' s',
    type_check_store tb s ->
    well_typed_decl tb d tb' ->
    eval_decl s d (S_Normal s') ->
    type_check_store tb' s'.
Proof.
    intros.
    induction H0.
  - inversion H1; subst.
    rewrite <- H3 in H6; inversion H6; subst.
    destruct t; 
    constructor; auto.
  - inversion H1; subst.
    + rewrite <- H3 in H7; inversion H7; subst.
      specialize (eval_type_reserve _ _ _ _ _ H H10 H4); intros hz1.
      destruct v; destruct t; try rm_contradict;
      constructor; auto.
    + rewrite <- H3 in H9; 
      inversion H9.
Qed.

Lemma typed_store_reserve_decls: forall tl tb s d tb' s',
    type_check_store tb s ->
    well_typed_decls tb (d :: tl) tb' ->
    eval_decls s (d :: tl) (S_Normal s') ->
    type_check_store tb' s'.
Proof.
    induction tl; intros.
  - inversion H0; subst.
    inversion H1; subst.
    inversion H7; subst.
    inversion H9; subst.
    specialize (typed_store_reserve_decl _ _ _ _ _ H H5 H6); auto.
  - inversion H0; subst.
    inversion H1; subst.
    specialize (typed_store_reserve_decl _ _ _ _ _ H H5 H6); intros hz1.
    specialize (IHtl _ _ _ _ _ hz1 H7 H9).
    assumption.
Qed.

Lemma mode_mapping_consis_decl: forall tb s m d tb' m' s',
    type_check_store tb s ->
    mode_mapping tb s m ->
    well_typed_decl tb d tb' ->
    well_defined_decl m d m' ->
    eval_decl s d (S_Normal s') ->
    mode_mapping tb' s' m'.
Proof.
    intros.
    induction H1; subst.
  - inversion H2; subst;
    rewrite <- H5 in H6; inversion H6.
    inversion H3; subst.
    rewrite <- H5 in H8; inversion H8.
    destruct t;
    constructor; auto. 
  - inversion H2; subst;
    rewrite <- H5 in H7; inversion H7; subst.
    inversion H3; subst.
    + rewrite <- H5 in H10; inversion H10; subst.
      specialize (eval_type_reserve _ _ _ _ _ H H13 H6); intros hz1.
      destruct v; destruct t; try rm_contradict;
      constructor; auto.
    + rewrite <- H5 in H12; 
      inversion H12.
Qed.

Lemma mode_mapping_consis_decls: forall tl tb s m d tb' m' s',
    type_check_store tb s ->
    mode_mapping tb s m ->
    well_typed_decls tb (d :: tl) tb' ->
    well_defined_decls m (d :: tl) m' ->
    eval_decls s (d :: tl) (S_Normal s') ->
    mode_mapping tb' s' m'.
Proof.
    induction tl; intros;
    inversion H1; subst;
    inversion H2; subst;
    inversion H3; subst.
  - inversion H9; subst;
    inversion H11; subst;
    inversion H13; subst.
    specialize (mode_mapping_consis_decl _ _ _ _ _ _ _ H H0 H7 H8 H10); auto.
  - specialize (typed_store_reserve_decl _ _ _ _ _ H H7 H10); intros hz1.
    specialize (mode_mapping_consis_decl _ _ _ _ _ _ _ H H0 H7 H8 H10); intros hz2.
    specialize (IHtl _ _ _ _ _ _ _ hz1 hz2 H9 H11 H13).
    assumption.
Qed.


(****************************************************)
(****************************************************)

(**
    for any expression e, and for any variable x, whenever it's 
    initialized in istate1 it's also initialized in state istate2, 
    if e is well-defined (all used variables have been initialized) 
    in state istate1, then it should also be well-defined in state 
    istate2;
*)
Lemma initializationMap_expr: forall istate1 e istate2,
     well_defined_expr istate1 e ->   
     (forall x md, fetch2 x istate1 = Some (Init, md) -> fetch2 x istate2 = Some (Init, md)) ->
     well_defined_expr istate2 e.
Proof.
    intros istate1 e istate2 h1.
    revert istate2.
    induction e;
    intros istate2 h2.
  - destruct l; constructor.
  - inversion h1; subst.
    specialize (h2 _ _ H1).
    econstructor. apply h2.
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

Ltac distr_univ_qualifier :=
    match goal with (* move the universally qualified variables x and md into inside its elements *)
    | [h: forall (x: ?T1) (md: ?T2), ?A1 /\ ?A2 |- _ ] => 
        assert (ha1: (forall (x: T1) (md: T2), A1) /\ (forall (x: T1) (md: T2), A2));
        [split; intros x_1 md_1 hz_1; specialize (h x_1 md_1); destruct h; intuition | ]; clear h; destruct ha1
    end.

(** 
    this is an extended version of initializationMap_expr, 
    which is used to prove lemma: ''initializationMap_stmt'' 
*)
Lemma initializationMap_expr1: forall istate1 e istate2,
     well_defined_expr istate1 e ->   
     (forall x md, (fetch2 x istate1 = Some (Init, md) -> fetch2 x istate2 = Some (Init, md)) /\
                   (fetch2 x istate1 = Some (Uninit, md) -> exists istate, fetch2 x istate2 = Some (istate, md))) ->
     well_defined_expr istate2 e.
Proof.
    intros.
    distr_univ_qualifier.
    specialize (initializationMap_expr _ _ _ H H0); intros hz1.
    assumption.
Qed.

(**
    for any variable x, whenever it's initialized in state istate1 
    it's also initialized in state istate2, and for any variable x, 
    whenever it's initialized in state istate2 it's also initialized 
    in state istate3, then, for any variable x, whenever it's 
    initialized in state istate1 it's also initialized in state istate3;
*)
Lemma fetch2_transitive: forall istate1 istate2 istate3,
    (forall x md,
      (fetch2 x istate1 = Some (Init, md) -> fetch2 x istate2 = Some (Init, md)) /\
      (fetch2 x istate1 = Some (Uninit, md) ->
       exists istate, fetch2 x istate2 = Some (istate, md))) ->       
    (forall x md,
      (fetch2 x istate2 = Some (Init, md) -> fetch2 x istate3 = Some (Init, md)) /\
      (fetch2 x istate2 = Some (Uninit, md) ->
       exists istate, fetch2 x istate3 = Some (istate, md))) ->
    (forall x md,
      (fetch2 x istate1 = Some (Init, md) -> fetch2 x istate3 = Some (Init, md)) /\
      (fetch2 x istate1 = Some (Uninit, md) ->
       exists istate, fetch2 x istate3 = Some (istate, md))).
Proof.
    intros istate1 istate2 istate3 h1 h2.
    intros x md.
    repeat distr_univ_qualifier.
    split; intros hz1.
  - specialize (H1 _ _ hz1).
    specialize (H _ _ H1).
    assumption.
  - specialize (H2 _ _ hz1).
    destruct H2.
    destruct x0.
    + specialize (H _ _ H2).
       exists Init; assumption.
    + specialize (H0 _ _ H2).
       assumption.
Qed.

Lemma fetch_same_mode: forall istate1 istate2 im1 im2 x md1 md2,
    (forall x md, (fetch2 x istate1 = Some (Init, md) -> fetch2 x istate2 = Some (Init, md))) ->
     (forall x md, (fetch2 x istate1 = Some (Uninit, md) -> exists im, fetch2 x istate2 = Some (im, md))) ->
    fetch2 x istate1 = Some (im1, md1) ->
    fetch2 x istate2 = Some (im2, md2) ->
    md1 = md2.
Proof.
    intros.
    destruct im1.
  - specialize (H _ _ H1).
    rewrite H in H2; inversion H2; subst; 
    auto.
  - specialize (H0 _ _ H1).
    destruct H0.
    rewrite H0 in H2; inversion H2; subst;
    auto.
Qed.


(**
    if istate1 is a subset of istate2 with respect to initialization 
    state, and istate1' is the resulting initialization state after 
    executing statement c from initialization state istate1, and 
    istate' is the resulting initialization state after executing 
    statement c from initialization state istate2, then istate1' 
    should be a subset of istate2'; 
*)
Lemma wd_fetch2_sync: forall c istate1 istate1' istate2 istate2',
    well_defined_stmt istate1 c istate1' ->
    well_defined_stmt istate2 c istate2' ->
    (forall x md, (fetch2 x istate1 = Some (Init, md) -> fetch2 x istate2 = Some (Init, md)) /\
                  (fetch2 x istate1 = Some (Uninit, md) -> exists istate, fetch2 x istate2 = Some (istate, md))) ->
    (forall x md, (fetch2 x istate1' = Some (Init, md) -> fetch2 x istate2' = Some (Init, md)) /\
                  (fetch2 x istate1' = Some (Uninit, md) -> exists istate, fetch2 x istate2' = Some (istate, md))).
Proof.
    induction c;
    intros istate1 istate1' istate2 istate2' h1 h2 h3.
  - distr_univ_qualifier.
    inversion h1; subst.
    inversion h2; subst.
    intros x md1.    
    specialize (fetch_same_mode _ _ _ _ _ _ _ H H0 H6 H10); intros hz1.
    subst.
    split; intros hz1;
    specialize (update2_in1 _ _ _ _ _ _ H9 hz1); intros hz2;
    destruct hz2 as [hz3 | hz4].
    + destruct hz3. inversion H2; subst.
       specialize (update2_fetch2_new _ _ _ _  H13). 
       auto.
    + rm_exists.
       specialize (H _ _ H2).
       specialize (update2_fetch2_old _ _ _ _ _ H13 H1); intros hz3.
       rewrite H in hz3.
       assumption.
    + inversion hz3.
       inversion H2.
    + rm_exists.
       specialize (H0 _ _ H2).
       specialize (update2_fetch2_old _ _ _ _ _ H13 H1); intros hz3.
       rewrite hz3.
       assumption. 
  - distr_univ_qualifier.
    inversion h1; subst.
    inversion h2; subst.
    intros x md.
    split; intros hz1.
    specialize (H _ _ hz1); assumption.
    specialize (H0 _ _ hz1); assumption.
  - distr_univ_qualifier.
    inversion h1; subst.
    inversion h2; subst.
    intros x md.
    split; intros hz1.
    specialize (H _ _ hz1); assumption.
    specialize (H0 _ _ hz1); assumption.
  - inversion h1; subst.
    inversion h2; subst.
    intros x md.
    split; intros hz1;
    specialize (IHc1 _ _ _ _ H4 H6 h3);
    specialize (IHc2 _ _ _ _ H5 H7 IHc1);
    repeat distr_univ_qualifier.
    + apply H1; assumption.
    + apply H2; assumption.
Qed.


(**
    if statement c is well-defined (all its used variables have been 
    initialized) under the state istate1, and istate' is the resulting 
    initialization state after executing statement c from initialization 
    state istate1, and istate1 is a subset of istate2 with respect to 
    initialization state, then statement c should be also well-defined 
    under the state istate2;
*)
Lemma initializationMap_stmt: forall istate1 c istate1' istate2,
     well_defined_stmt istate1 c istate1' ->   
     (forall x md, (fetch2 x istate1 = Some (Init, md) -> fetch2 x istate2 = Some (Init, md)) /\
                   (fetch2 x istate1 = Some (Uninit, md) -> exists im, fetch2 x istate2 = Some (im, md))) ->
     exists istate2', well_defined_stmt istate2 c istate2'.
Proof.
    intros istate1 c istate1' istate2 h1.
    revert istate2.
    induction h1;
    intros istate2 h2.
  - specialize (initializationMap_expr1 _ _ _ H h2); intros hz1.
    distr_univ_qualifier.
    assert (hz2: exists istate, update2 istate2 x (Init, md) = Some istate).
    + destruct i.
       * specialize (H3 _ _ H0).
          specialize (fetch2_update2 _ _ _ (Init, md) H3); intros hz3.
          assumption.
       * specialize (H4 _ _ H0).
          destruct H4.
          specialize (fetch2_update2 _ _ _ (Init, md) H4); intros hz3.
          assumption.
    + destruct hz2.
       exists x0.
       assert (hz2: exists im, fetch2 x istate2 = Some (im, md)).
       destruct i.
       specialize (H3 _ _ H0). exists Init; apply H3.
       specialize (H4 _ _ H0). assumption.
       destruct hz2.
       econstructor; auto. apply H6.
       assumption. assumption.
  - specialize (IHh1_1 _ h2).
    rm_exists.
    specialize (wd_fetch2_sync _ _ _ _ _ h1_1 H h2); intros hz1.
    specialize (IHh1_2 x hz1).
    rm_exists.
    exists x0.
    apply WD_Sequence with (m' := x);
    assumption.
  - exists istate2.
    specialize (IHh1 _ h2).
    rm_exists.
    apply WD_If with (m' := x); auto.
    distr_univ_qualifier.
    specialize (initializationMap_expr _ _ _ H H1); intros hz1.
    assumption.
  - exists istate2.
    specialize (IHh1 _ h2).
    rm_exists.
    apply WD_While_Loop with (m' := x); auto.
    distr_univ_qualifier.
    specialize (initializationMap_expr _ _ _ H H1); intros hz1.
    assumption.
Qed.

(**
    if c is well-defined (all its used variables have been initialized) 
    in state istate, and istate' is its resulting initialization state 
    after statement c, then for any variable x that's initialized in 
    state istate should also be initialized in state istate'; 
*)
Lemma initializationMap_inc: forall istate c istate',
     well_defined_stmt istate c istate' ->   
     (forall x md, (fetch2 x istate = Some (Init, md) -> fetch2 x istate' = Some (Init, md)) /\
                   (fetch2 x istate = Some (Uninit, md) -> exists im, fetch2 x istate' = Some (im, md))).
Proof.
    intros istate c istate' h1.
    induction h1;
    intros x0 md0.
  - remember (beq_nat x0 x) as eq;
    symmetry in Heqeq;
    destruct eq as [eq1 | eq2].
    + apply beq_nat_true in Heqeq; subst.
       specialize (update2_fetch2_new _ _ _ _ H2); intros hz1.
       split; intros;
       rewrite H0 in H3; inversion H3; subst.
       * assumption.
       * exists Init; assumption.
    + apply beq_nat_false in Heqeq.
       specialize (update2_fetch2_old _ _ _ _ _ H2 Heqeq); intros hz1.
       split; intros; rewrite hz1. 
       * assumption.
       * exists Uninit; assumption.
  - repeat distr_univ_qualifier.
    split; intros hz1.
    + apply H.
       apply H1.
       assumption.
    + specialize (H2 _ _ hz1).
       rm_exists.
       destruct x.
       specialize (H _ _ H3).
       exists Init; assumption.
       specialize (H0 _ _ H3).
       assumption.
  - split; auto.
    intros.
    exists Uninit.
    assumption.
  - split;auto.
    intros.
    exists Uninit.
    assumption.
Qed.

(**
    it's used to prove the lemma update_consis, refer to update_consis 
    for its meanings;
*)
Lemma update_consis0: forall tb s istate x v s1 istate1 md t,
    mode_mapping tb s istate -> 
    update s x (Value v) = Some s1 ->
    mode_mapping tb s1 istate1 ->
    lookup x tb = Some (md, t) ->
    (update2 istate x (Init, md)) = Some istate1.
Proof.
    intros tb s istate x v s1 istate1 md t h1.
    revert x v s1 istate1 md t.
    induction h1;
    intros x'0 v'0 s1 istate1 md t h2 h3 h4.
  - inversion h2.
  - unfold update in h2.
    remember (beq_nat x'0 x) as eq.
    fold update in h2.
    destruct eq;
    unfold lookup in h4; rewrite <- Heqeq in h4.
    + inversion h2; subst;
       inversion h3; subst.
       specialize (mode_mapping_unique _ _ _ _ h1 H5); intros hz1; subst.
       unfold update2; rewrite <- Heqeq. 
       inversion h4; subst.
       reflexivity.
    + remember (update s x'0 (Value v'0)) as z.
       symmetry in Heqz.
       destruct z.
       inversion h2; subst;
       inversion h3; subst.
       fold lookup in h4.
       specialize (IHh1 _ _ _ _ _ _ Heqz H5 h4).
       unfold update2; rewrite <- Heqeq.
       fold update2. 
       rewrite IHh1; reflexivity.
       inversion h2.
  - unfold update in h2.
    remember (beq_nat x'0 x) as eq.
    fold update in h2.
    destruct eq;
    unfold lookup in h4; rewrite <- Heqeq in h4.
    + inversion h2; subst;
       inversion h3; subst.
       specialize (mode_mapping_unique _ _ _ _ h1 H5); intros hz1; subst.
       unfold update2; rewrite <- Heqeq. 
       inversion h4; subst.
       reflexivity.
    + remember (update s x'0 (Value v'0)) as z.
       symmetry in Heqz.
       destruct z.
       inversion h2; subst;
       inversion h3; subst.
       fold lookup in h4.
       specialize (IHh1 _ _ _ _ _ _ Heqz H5 h4).
       unfold update2; rewrite <- Heqeq.
       fold update2. 
       rewrite IHh1; reflexivity.
       inversion h2.
  - unfold update in h2.
    remember (beq_nat x'0 x) as eq.
    fold update in h2.
    destruct eq;
    unfold lookup in h4; rewrite <- Heqeq in h4.
    + inversion h2; subst;
       inversion h3; subst.
       specialize (mode_mapping_unique _ _ _ _ h1 H5); intros hz1; subst.
       unfold update2; rewrite <- Heqeq. 
       inversion h4; subst.
       reflexivity.
    + remember (update s x'0 (Value v'0)) as z.
       symmetry in Heqz.
       destruct z.
       inversion h2; subst;
       inversion h3; subst.
       fold lookup in h4.
       specialize (IHh1 _ _ _ _ _ _ Heqz H4 h4).
       unfold update2; rewrite <- Heqeq.
       fold update2. 
       rewrite IHh1; reflexivity.
       inversion h2.
  - unfold update in h2.
    remember (beq_nat x'0 x) as eq.
    fold update in h2.
    destruct eq;
    unfold lookup in h4; rewrite <- Heqeq in h4.
    + inversion h2; subst;
       inversion h3; subst.
       specialize (mode_mapping_unique _ _ _ _ h1 H5); intros hz1; subst.
       unfold update2; rewrite <- Heqeq. 
       inversion h4; subst.
       reflexivity.
    + remember (update s x'0 (Value v'0)) as z.
       symmetry in Heqz.
       destruct z.
       inversion h2; subst;
       inversion h3; subst.
       fold lookup in h4.
       specialize (IHh1 _ _ _ _ _ _ Heqz H4 h4).
       unfold update2; rewrite <- Heqeq.
       fold update2. 
       rewrite IHh1; reflexivity.
       inversion h2.
Qed.


(**
    tb: a symbol table mapping from variable to a pair (type, in/out mode);
    s: a store mapping from variable to value;
    istate: is a mode table constructed from tb and s, which maps 
            from variable to a pair (initialization mode, in/out mode),
            for a variable x, if it's initialized according to the store s, 
            then it's initialization mode is "Init", otherwise, it's "Uninit";
    if we update the store s with variable x by a value v, and the 
    resulting state is s1, then the mode table istate1 constructed 
    from tb and s1 should be the same as istate'1 which is the 
    result of updating istate directly by (Init, md);
*)
Lemma update_consis: forall tb s istate x v s1 istate1 md t istate'1,
    mode_mapping tb s istate -> 
    update s x (Value v) = Some s1 ->
    mode_mapping tb s1 istate1 ->
    lookup x tb = Some (md, t) ->
    (update2 istate x (Init, md)) = Some istate'1 ->
    istate1 = istate'1.
Proof.
    intros.
    specialize (update_consis0 _ _ _ _ _ _ _ _ _ H H0 H1 H2); intros hz1.
    rewrite hz1 in H3; inversion H3; subst.
    reflexivity.
Qed.

Lemma mode_consis: forall tb s istate x md1 t im md2,
    mode_mapping tb s istate ->
    lookup x tb = Some (md1, t) ->
    fetch2 x istate = Some (im, md2) ->
    md1 = md2.
Proof.
    intros.
    induction H;
    [inversion H0 | | | | ];
    unfold lookup in H0;
    unfold fetch2 in H1;
    remember (beq_nat x x0) as eq;
    destruct eq;
    [ inversion H0; subst;
      inversion H1; subst;
      reflexivity |  |
      inversion H0; subst;
      inversion H1; subst;
      reflexivity | |
      inversion H0; subst;
      inversion H1; subst;
      reflexivity | |
      inversion H0; subst;
      inversion H1; subst;
      reflexivity | 
    ]; 
    fold lookup in H0; fold fetch2 in H1;
    apply IHmode_mapping; auto.
Qed.


(**
    tb: a symbol table mapping from variable to a pair (type, in/out mode);
    s: a store mapping from variable to value;
    istate: is a mode table constructed from tb and s, which maps 
            from variable to a pair (initialization mode, in/out mode),
            for a variable x, if it's initialized according to the 
            store s, then it's initialization mode is "Init", 
            otherwise, it's "Uninit";
    whenever we execute the statement c from state s1 to state s2 
    under the refence semantics eval_stmt, if istate1 is the mode 
    table constructed from tb and s1 and istate2 is the mode table 
    constructed from tb and s2, then istate1 should be a subset of 
    istate2 with respect to initialization mode and in/out mode, 
    because the statement will cause uninitialized variables to 
    initialized ones and will not change their in/out mode;
*)
Lemma initialization_inc: forall s1 c s2 tb istate1 istate2,
    eval_stmt s1 c (S_Normal s2) ->
    type_check_store tb s1 ->
    well_typed_stmt tb c ->
    mode_mapping tb s1 istate1 ->
    mode_mapping tb s2 istate2 ->
     (forall x md, (fetch2 x istate1 = Some (Init, md) -> fetch2 x istate2 = Some (Init, md)) /\
                   (fetch2 x istate1 = Some (Uninit, md) -> exists im, fetch2 x istate2 = Some (im, md))).
Proof.
    intros s1 c s2 tb istate1 istate2 h1.
    revert tb istate1 istate2.
    remember (S_Normal s2) as v; revert Heqv; revert s2.
    induction h1;
    intros s'2 h2 tb istate1 istate2 h3 h4 h5 h6;
    try (inversion h2; subst);
    inversion h4; subst.
  - specialize (update_consis0 _ _ _ _ _ _ _ _ _ h5 H0 h6 H4); intros hz1.
    intros; split; intros;
    remember (beq_nat x0 x) as eq; symmetry in Heqeq;
    destruct eq.
    * apply beq_nat_true in Heqeq. subst. 
      specialize (mode_consis _ _ _ _ _ _ _ _ h5 H4 H1); intros hz2; subst. 
      specialize (update2_fetch2_new _ _ _ _ hz1); intros hz3.
      assumption.
   * apply beq_nat_false in Heqeq.
     specialize (update2_fetch2_old _ _ _ _ _ hz1 Heqeq); intros hz2.
     rewrite H1 in hz2.
     assumption.
    * apply beq_nat_true in Heqeq. subst. 
      specialize (mode_consis _ _ _ _ _ _ _ _ h5 H4 H1); intros hz2; subst. 
      specialize (update2_fetch2_new _ _ _ _ hz1); intros hz3.
      exists Init; assumption.
   * apply beq_nat_false in Heqeq.
     specialize (update2_fetch2_old _ _ _ _ _ hz1 Heqeq); intros hz2.
     rewrite H1 in hz2.
     exists Uninit; assumption.
  - specialize (type_reserve_stmt _ _ _ _ h3 H3 h1_1); intros hz1.
    specialize (mode_mapping_exists _ _ hz1); intros hz2.
    destruct hz2.
    assert (a1: S_Normal s1 = S_Normal s1); auto.
    assert (a2: S_Normal s'2 = S_Normal s'2); auto.
    specialize (IHh1_1 s1 a1 tb istate1 x);
    specialize (IHh1_2 s'2 a2 tb x istate2); intuition;
    repeat distr_univ_qualifier.
    apply H4. apply H2; assumption.
    specialize (H7 _ _ H1). destruct H7.
    destruct x1.
    * specialize (H4 _ _ H7). exists Init; auto.
    * specialize (H6 _ _ H7); auto.
  - assert (a1: S_Normal s'2 = S_Normal s'2); auto.
    specialize (IHh1 s'2 a1 tb istate1 istate2); intuition.
  - specialize (mode_mapping_unique _ _ _ _ h5 h6); intros hz1.
    subst. 
    intros; split; intros; auto.
    exists Uninit; assumption.
  - specialize (type_reserve_stmt _ _ _ _ h3 H6 h1_1); intros hz1.
    specialize (mode_mapping_exists _ _ hz1); intros hz2.
    destruct hz2.
    assert (a1: S_Normal s1 = S_Normal s1); auto.
    assert (a2: S_Normal s'2 = S_Normal s'2); auto.    
    specialize (IHh1_1 s1 a1 tb istate1 x).
    specialize (IHh1_2 s'2 a2 tb x istate2); intuition;
    repeat distr_univ_qualifier.
    apply H5. apply H3; auto.
    specialize (H8 _ _ H2). destruct H8.
    destruct x1.
    * specialize (H5 _ _ H8). exists Init; auto.
    * specialize (H7 _ _ H8); auto.
  - specialize (mode_mapping_unique _ _ _ _ h5 h6); intros hz1.
    subst.
    intros; split; intros; auto.
    exists Uninit; auto.
Qed.


(**
    tb: a symbol table mapping from variable to a pair (type, in/out mode);
    s: a store mapping from variable to value;
    istate: is a mode table constructed from tb and s, which maps 
            from variable to a pair (initialization mode, in/out mode),
            for a variable x, if it's initialized according to the 
            store s, then it's initialization mode is "Init", 
            otherwise, it's "Uninit";
    when we define "well_defined_stmt", we adopt the following 
    strategy: for conditional and while loop, we do intersection on
    the initialization states generated on both branches; but 
    "eval_stmt" will take one branch to execute from state s to s', 
    so the mode table istate' is a subset of the mode table istate1 
    constructed from tb and s';
*)
Lemma eval_stmt_greater: forall c s s' tb istate istate' istate1,
     eval_stmt s c (S_Normal s') ->
     type_check_store tb s ->
     well_typed_stmt tb c -> 
     mode_mapping tb s istate->
     well_defined_stmt istate c istate' -> 
     mode_mapping tb s' istate1 ->
     (forall x md, (fetch2 x istate' = Some (Init, md) -> fetch2 x istate1 = Some (Init, md)) /\
                   (fetch2 x istate' = Some (Uninit, md) -> exists im, fetch2 x istate1 = Some (im, md))).
Proof.
    induction c;
    intros s s' tb istate istate' istate1 h1 h2 h3 h4 h5 h6;
    inversion h1; subst;
    inversion h3; subst;
    inversion h5; subst.
  - specialize (mode_consis _ _ _ _ _ _ _ _ h4 H3 H8); intros hz1; subst.
    specialize (update_consis _ _ _ _ _ _ _ _ _ _  h4 H5 h6 H3 H11); intros hz1.
    subst.
    intros; split; intros; auto.
    exists Uninit; assumption.
  - specialize (IHc _ _ _ _ _ _ H5 h2 H6 h4 H9 h6).
    specialize (initializationMap_inc _ _ _ H9); intros hz1.
    specialize (fetch2_transitive _ _ _ hz1 IHc); intros hz2.
    assumption.
  - specialize (mode_mapping_unique _ _ _ _ h4 h6); intros hz1.
    subst.
    intros; split; intros; auto.
    exists Uninit; assumption.
  - specialize (type_reserve_stmt _ _ _ _ h2 H7 H5); intros hz1.
    specialize (mode_mapping_exists _ _ hz1); intros hz2.
    destruct hz2.
    specialize (IHc _ _ _ _ _ _ H5 h2 H7 h4 H10 H).
    specialize (initializationMap_inc _ _ _ H10); intros hz2.
    specialize (fetch2_transitive _ _ _ hz2 IHc); intros hz3.
    specialize (initialization_inc _ _ _ _ _ _ H6 hz1 h3 H h6); intros hz4.
    specialize (fetch2_transitive _ _ _ hz3 hz4); intros hz5.
    assumption.
  - specialize (mode_mapping_unique _ _ _ _ h4 h6); intros hz1.
    subst.
    intros; split; intros; auto.
    exists Uninit; assumption.
  - specialize (type_reserve_stmt _ _ _ _ h2 H2 H4); intros hz1.
    specialize (mode_mapping_exists _ _ hz1); intros hz2.
    destruct hz2.
    specialize (IHc1 _ _ _ _ _ _ H4 h2 H2 h4 H8 H).
    specialize (initializationMap_stmt _ _ _ _ H9 IHc1); intros hz3.
    destruct hz3.
    specialize (IHc2 _ _ _ _ _ _ H5 hz1 H6 H H0 h6).
    specialize (wd_fetch2_sync _ _ _ _ _ H9 H0 IHc1); intros hz4.
    specialize (fetch2_transitive _ _ _ hz4 IHc2); auto.
Qed.


(* destruct a disjunction of the following type in the hypothesis, among its disjunct elements, most of
    which can be removed quickly:
    IHs0 : (exists s' : store,
          SNormal s1 = SNormal s' /\
          eval_stmt_with_checks ls2 s c1 (SNormal s')) \/
       SNormal s1 = SException /\ eval_stmt_with_checks ls2 s c1 SException \/
       SNormal s1 = SUnterminated
*)
Ltac destruct_disj IH :=
    destruct IH as [IH0 | [IH1 | IH2]];
    [destruct IH0 as [s'1 IH1] | | inversion IH2];
    destruct IH1 as [IH11 IH12]; 
    [inversion IH11; subst | inversion IH11].


(** 
    This is a help lemma to prove the theorem: well_formed_stmt,  
    refer to well_formed_stmt for its meanings;
    it's a little difficult to prove the theorem "well_formed_stmt" 
    directly, becuase induction on any of its assumptions cannot lead 
    to proving the theorem;
*)

Lemma well_formed_stmt0: forall k s c tb m0 m1 cks0 cks1 max,
    type_check_store tb s ->
    mode_mapping tb s m0 -> (* m: a map from variable to its initialization state and in/out mode *)
    well_defined_stmt m0 c m1 ->
    well_typed_stmt tb c ->
    well_checked_stmt cks0 c cks1 ->
    ast_nums_lt cks0 (get_ast_num_stmt c) ->
    ast_num_inc_stmt c max ->
    (exists s', f_eval_stmt k s c = (S_Normal s') /\ eval_stmt_with_checks cks1 s c (S_Normal s')) \/ 
    (f_eval_stmt k s c = S_Run_Time_Error /\ eval_stmt_with_checks cks1 s c S_Run_Time_Error) \/ 
    f_eval_stmt k s c = S_Unterminated.
Proof.
    intros k s c.
    functional induction (f_eval_stmt k s c);
    intros tb m0 m1 cks0 cks1 max h1 h2 h3 h4 h5 h6 h7;
    try match goal with
    | [ |- ?G1 \/ ?G2 \/ ?T = ?T ] => right; right; reflexivity
    | [ |- (exists s', S_Normal ?s = S_Normal s' /\ ?G1) \/ ?G2 \/ ?G3 ] => left; exists s; split; auto
    | [ |- ?G1 \/ (?T = ?T /\ ?G2) \/ ?G3 ] => right; left; split; auto
    end;
    simpl in h6;
    inversion h3; subst;
    inversion h4; subst;
    inversion h5; subst;
    inversion h7; subst.
  - (* Sassign: return normal state *)
    econstructor.
    Focus 2. apply e3.
    specialize (f_eval_expr_correct1 _ _ _ e2); intros hz1.
    specialize (ast_nums_lt_trans _ _ _ h6 H12); intros hz2.
    specialize (eval_expr_with_checks_complete _ _ _ _ _ _ hz1 H10 hz2 H5); auto.
  - (* Sassign: proof term with contradictory hypothesis *)
    specialize (valid_update _ _ _ _ _ v h1 h4); intros hz1.
    destruct hz1 as [s' hz1].
    rewrite e3 in hz1; inversion hz1.
  - (* Sassign: return exception *)
    econstructor.
    specialize (f_eval_expr_correct2 _ _ e2); intros hz1.
    specialize (ast_nums_lt_trans _ _ _ h6 H12); intros hz2.
    specialize (eval_expr_with_checks_complete _ _ _ _ _ _ hz1 H10 hz2 H5); auto.
  - (* Sassign: proof term with contradictory hypothesis *)
    specialize (ast_nums_lt_trans _ _ _ h6 H12); intros hz1.
    specialize (well_formed_expr _ _ _ _ _ _ _ _ h1 h2 H2 H8 H10 hz1 H5); intros hz2.
    destruct hz2 as [v hz2].
    specialize (f_eval_expr_complete _ _ _ hz2); intros hz3.
    rewrite e2 in hz3.
    
    specialize (eval_expr_state _ _ _ hz2); intros hz4.
    destruct hz4 as [ [v0 hz5] | hz5]; subst;
    inversion hz5.
  - (* Sseq *)
    specialize (f_eval_stmt_correct1 _ _ _ _ e1); intros hz1.
    specialize (type_reserve_stmt _ _ _ _ h1 H2 hz1); intros hz2.
    specialize (mode_mapping_exists _ _ hz2); intros hz3.
    destruct hz3 as [m'1 hz3].
    specialize (ast_nums_lt_trans _ _ _ h6 H12); intros hz4.
    specialize (lt_trans_stmt _ _ _ _ _ H8 hz4 H3 H15); intros hz5.
    specialize (IHs0 _ _ _ _ _ _ h1 h2 H4 H2 H8 hz4 H3).
    
    specialize (eval_stmt_greater _ _ _ _ _ _ _ hz1 h1 H2 h2 H4 hz3); intros hz6.
    specialize (initializationMap_stmt _ _ _ _ H5 hz6); intros hz7.
    destruct hz7. clear hz6.
    
    specialize (IHs1 _ _ _ _ _ _ hz2 hz3 H H6 H9 hz5 H7).
    rewrite e1 in IHs0.

    destruct_disj IHs0.
    specialize (subset_refl (max + 1) cks1); intros hz6.
    specialize (help2 _ _ _ _ _ _ H9 H7 hz5 H15 hz6); intros hz7.
    specialize (eval_stmt_with_checks_fixed _ _ _ _ _ _ _ IH12 hz7 H8 hz4 H3); intros hz8.
    destruct IHs1 as [IHs1_1 | [IHs1_1 | IHs1_1]].
    + destruct IHs1_1. destruct H0.
       left. exists x0.
       split; auto.
       econstructor.
       apply hz8. assumption.
    + destruct IHs1_1.
       right. left.
       split; auto.
       eapply eval_Sequence2.
       apply hz8. assumption.
    + right. right.
       assumption.
  - (* Sseq: return exception *)
    specialize (ast_nums_lt_trans _ _ _ h6 H12); intros hz1.
    specialize (lt_trans_stmt _ _ _ _ _ H8 hz1 H3 H15); intros hz2.
    specialize (IHs0 _ _ _ _ _ _ h1 h2 H4 H2 H8 hz1 H3). 
    rewrite e1 in IHs0.
    destruct_disj IHs0.
    specialize (subset_refl (max + 1) cks1); intros hz3.
    specialize (help2 _ _ _ _ _ _ H9 H7 hz2 H15 hz3); intros hz4.
    specialize (eval_stmt_with_checks_fixed _ _ _ _ _ _ _ IH12 hz4 H8 hz1 H3); intros hz5.
    + constructor. assumption.
  - (* Sseq: proof term with contradictory hypothesis *)
    specialize (ast_nums_lt_trans _ _ _ h6 H12); intros hz1.
    specialize (lt_trans_stmt _ _ _ _ _ H8 hz1 H3 H15); intros hz2.
    specialize (IHs0 _ _ _ _ _ _ h1 h2 H4 H2 H8 hz1 H3). 
    rewrite e1 in IHs0.
    destruct_disj IHs0.
  - (* Sifthen_true: return normal state *)
    specialize (ast_nums_lt_trans _ _ _ h6 H12); intros hz1.
    specialize (lt_trans_expr _ _ _ _ _ H8 hz1 H3 H15); intros hz2.
    specialize (f_eval_expr_correct1 _ _ _ e1); intros hz3.
    specialize (eval_expr_with_checks_complete _ _ _ _ _ _ hz3 H8 hz1 H3); intros hz4.
    specialize (subset_refl (max + 1) cks1); intros hz5.
    specialize (help2 _ _ _ _ _ _ H9 H7 hz2 H15 hz5); intros hz6.
    specialize (eval_expr_with_checks_fixed _ _ _ _ _ _ _ hz4 hz6 H8 hz1 H3); intros hz7.
    specialize (IHs0 _ _ _ _ _ _ h1 h2 H5 H6 H9 hz2 H7).
    
    destruct IHs0 as [IH0_1 | [IH0_1 | IH0_1]].
    + destruct IH0_1. destruct H.
       left. exists x.
       split; auto.
       econstructor; auto.
    + destruct IH0_1.
       right. left.
       split; auto.
       eapply eval_If_True; auto.
    + right. right.
       assumption.
  - (* Sifthen_false: return normal state *)
    specialize (ast_nums_lt_trans _ _ _ h6 H12); intros hz1.
    specialize (lt_trans_expr _ _ _ _ _ H8 hz1 H3 H15); intros hz2.
    specialize (f_eval_expr_correct1 _ _ _ e1); intros hz3.
    specialize (eval_expr_with_checks_complete _ _ _ _ _ _ hz3 H8 hz1 H3); intros hz4.
    specialize (subset_refl (max + 1) cks1); intros hz5.
    specialize (help2 _ _ _ _ _ _ H9 H7 hz2 H15 hz5); intros hz6.
    specialize (eval_expr_with_checks_fixed _ _ _ _ _ _ _ hz4 hz6 H8 hz1 H3); intros hz7.
    eapply eval_If_False.
    assumption.    
  - (* Sifthen: return exception *)
    specialize (ast_nums_lt_trans _ _ _ h6 H12); intros hz1.
    specialize (lt_trans_expr _ _ _ _ _ H8 hz1 H3 H15); intros hz2.
    specialize (f_eval_expr_correct2 _ _ e1); intros hz3.
    specialize (eval_expr_with_checks_complete _ _ _ _ _ _ hz3 H8 hz1 H3); intros hz4.
    specialize (subset_refl (max + 1) cks1); intros hz5.
    specialize (help2 _ _ _ _ _ _ H9 H7 hz2 H15 hz5); intros hz6.
    specialize (eval_expr_with_checks_fixed _ _ _ _ _ _ _ hz4 hz6 H8 hz1 H3); intros hz7.
    constructor; auto.
  - (* Sifthen: proof term with contradictory hypothesis *)
    specialize (ast_nums_lt_trans _ _ _ h6 H12); intros hz1.
    specialize (well_formed_expr _ _ _ _ _ _ _ _ h1 h2 H4 H2 H8 hz1 H3); intros hz2.
    destruct hz2 as [v hz2].
    specialize (f_eval_expr_complete _ _ _ hz2); intros hz3.
    specialize (eval_expr_state _ _ _ hz2); intros hz4.
    destruct hz4 as [ [v0 hz5] | hz5]; subst;
    rewrite hz5 in y.    
    + rewrite hz5 in hz2.
       specialize (eval_type_reserve _ _ _ _ _ h1 hz2 H2); intros hz6.
       destruct v0; inversion hz6.
       destruct b0; inversion y.
    + inversion y.
  - (* Swhile_true: return normal state *)
    specialize (ast_nums_lt_trans _ _ _ h6 H12); intros hz1.
    specialize (lt_trans_expr _ _ _ _ _ H8 hz1 H3 H15); intros hz2.
    specialize (f_eval_expr_correct1 _ _ _ e1); intros hz3.
    specialize (eval_expr_with_checks_complete _ _ _ _ _ _ hz3 H8 hz1 H3); intros hz4.
    specialize (subset_refl (max + 1) cks1); intros hz5.
    specialize (help2 _ _ _ _ _ _ H9 H7 hz2 H15 hz5); intros hz6.
    specialize (eval_expr_with_checks_fixed _ _ _ _ _ _ _ hz4 hz6 H8 hz1 H3); intros hz7.
    specialize (IHs0 _ _ _ _ _ _ h1 h2 H5 H6 H9 hz2 H7).

    specialize (f_eval_stmt_correct1 _ _ _ _ e2); intros hz8.
    specialize (type_reserve_stmt _ _ _ _ h1 H6 hz8); intros hz9.
 
    specialize (type_reserve_stmt _ _ _ _ h1 H6 hz8); intros hz10.
    specialize (mode_mapping_exists _ _ hz10); intros hz11.
    destruct hz11.
    simpl in IHs1.
    assert (a1: well_defined_stmt x (S_While_Loop ast_num b c0) x).
    specialize (initialization_inc _ _ _ _ _ _ hz8 h1 H6 h2 H); intros ha1.
    specialize (initializationMap_expr1 _ _ _ H4 ha1); intros ha1_1.
    specialize (initializationMap_stmt _ _ _ _ H5 ha1); intros ha1_2.
    destruct ha1_2.
    apply WD_While_Loop with (m' := x0); auto.

    specialize (IHs1 _ _ _ _ _ _ hz9 H a1 h4 h5 h6 h7).
    rewrite e2 in IHs0.

    destruct_disj IHs0.
    destruct IHs1 as [IHs1_1 | [IHs1_1 | IHs1_1]].
    + destruct IHs1_1. destruct H0.
       left. exists x0.
       split; auto.
       econstructor; auto.
       apply IH12. assumption.
    + destruct IHs1_1.
       right. left.
       split; auto.
       eapply eval_While_Loop_True2; auto.
       apply IH12. assumption.
    + right. right.
       assumption.
  - (* Swhile: return exception *)
    specialize (ast_nums_lt_trans _ _ _ h6 H12); intros hz1.
    specialize (lt_trans_expr _ _ _ _ _ H8 hz1 H3 H15); intros hz2.
    specialize (f_eval_expr_correct1 _ _ _ e1); intros hz3.
    specialize (eval_expr_with_checks_complete _ _ _ _ _ _ hz3 H8 hz1 H3); intros hz4.
    specialize (subset_refl (max + 1) cks1); intros hz5.
    specialize (help2 _ _ _ _ _ _ H9 H7 hz2 H15 hz5); intros hz6.
    specialize (eval_expr_with_checks_fixed _ _ _ _ _ _ _ hz4 hz6 H8 hz1 H3); intros hz7.
    specialize (IHs0 _ _ _ _ _ _ h1 h2 H5 H6 H9 hz2 H7).
    
    rewrite e2 in IHs0.
    destruct_disj IHs0.
    eapply eval_While_Loop_True1; auto.
  - (* Swhile: proof term with contradictory hypothesis *)
    specialize (ast_nums_lt_trans _ _ _ h6 H12); intros hz1.
    specialize (lt_trans_expr _ _ _ _ _ H8 hz1 H3 H15); intros hz2.
    specialize (IHs0 _ _ _ _ _ _ h1 h2 H5 H6 H9 hz2 H7).    
    rewrite e2 in IHs0.
    destruct_disj IHs0.
  - (* Swhile_false: return normal state *)
    specialize (ast_nums_lt_trans _ _ _ h6 H12); intros hz1.
    specialize (lt_trans_expr _ _ _ _ _ H8 hz1 H3 H15); intros hz2.
    specialize (f_eval_expr_correct1 _ _ _ e1); intros hz3.
    specialize (eval_expr_with_checks_complete _ _ _ _ _ _ hz3 H8 hz1 H3); intros hz4.
    specialize (subset_refl (max + 1) cks1); intros hz5.
    specialize (help2 _ _ _ _ _ _ H9 H7 hz2 H15 hz5); intros hz6.
    specialize (eval_expr_with_checks_fixed _ _ _ _ _ _ _ hz4 hz6 H8 hz1 H3); intros hz7.
    eapply eval_While_Loop_False; auto.
  - (* Swhile: return exception *)
    specialize (ast_nums_lt_trans _ _ _ h6 H12); intros hz1.
    specialize (lt_trans_expr _ _ _ _ _ H8 hz1 H3 H15); intros hz2.
    specialize (f_eval_expr_correct2 _ _ e1); intros hz3.
    specialize (eval_expr_with_checks_complete _ _ _ _ _ _ hz3 H8 hz1 H3); intros hz4.
    specialize (subset_refl (max + 1) cks1); intros hz5.
    specialize (help2 _ _ _ _ _ _ H9 H7 hz2 H15 hz5); intros hz6.
    specialize (eval_expr_with_checks_fixed _ _ _ _ _ _ _ hz4 hz6 H8 hz1 H3); intros hz7.
    constructor; auto.
  - (* Swhile: proof term with contradictory hypothesis *)
    specialize (ast_nums_lt_trans _ _ _ h6 H12); intros hz1.
    specialize (well_formed_expr _ _ _ _ _ _ _ _ h1 h2 H4 H2 H8 hz1 H3); intros hz2.
    destruct hz2 as [v hz2].
    specialize (f_eval_expr_complete _ _ _ hz2); intros hz3.
    specialize (eval_expr_state _ _ _ hz2); intros hz4.
    destruct hz4 as [ [v0 hz5] | hz5]; subst;
    rewrite hz5 in y.    
    + rewrite hz5 in hz2.
       specialize (eval_type_reserve _ _ _ _ _ h1 hz2 H2); intros hz6.
       destruct v0; inversion hz6.
       destruct b0; inversion y.
    + inversion y.
Qed.

(** ** well_formed_stmt *)
(**
    well-formed means: well-typed, well-defined (all used variables 
    have been initialized) and well-checked (with right checks put 
    at the right places according to checking rules);

    for any well-formed statement c, starting from the initial state 
    s, it should either terminate in a valid state s' with respect to 
    the reference semantics eval_stmt or it never terminates;
*)


(** well-formed terminated statement should be correct with respect 
    to its reference semantics, in other words, for any well-formed 
    terminated statement c evaluated in two semantics environments 
    "eval_stmt_with_checks" and "eval_stmt", if they start with the 
    same initial state s, they should terminate in the same state s';
    "eval_stmt_with_checks" is the semantics for statement with 
    run time check flags as its passed in parameters;
    "eval_stmt" is the reference semantics where checks are always 
    performed according to the checking rules;
*)

Theorem well_formed_stmt: forall tb s m0 c m1 cks0 cks1 max k,
    type_check_store tb s ->
    mode_mapping tb s m0 -> (* m0: a map from variable to its initialization state and in/out mode *)
    well_defined_stmt m0 c m1 ->
    well_typed_stmt tb c ->
    well_checked_stmt cks0 c cks1 ->
    ast_nums_lt cks0 (get_ast_num_stmt c) ->
    ast_num_inc_stmt c max ->
    (exists s', eval_stmt_with_checks cks1 s c s' /\ 
                eval_stmt s c s') \/ 
    f_eval_stmt k s c = S_Unterminated.
Proof.
    intros.
    specialize (well_formed_stmt0 k _ _ _ _ _ _ _ _ H H0 H1 H2 H3 H4 H5); intros hz1.
    destruct hz1 as [hz2 | [hz2 | hz2]].
  - destruct hz2 as [s' [hz3 hz4]].
    specialize (f_eval_stmt_correct1 _ _ _ _ hz3); intros hz5.
    left; 
    exists (S_Normal s'); auto.
  - destruct hz2 as [hz3 hz4].
    specialize (f_eval_stmt_correct2 _ _ _ hz3); intros hz5.
    left;
    exists S_Run_Time_Error; auto.
  - right; assumption.
Qed.


(***********************************************************)
(***********************************************************)

Lemma well_formed_decl: forall tb s m d m' tb' cks cks' max,
    type_check_store tb s ->
    mode_mapping tb s m -> (* m: a map from variable to its initialization state and in/out mode *)
    well_defined_decl m d m' ->
    well_typed_decl tb d tb' ->
    well_checked_decl cks d cks' ->
    ast_nums_lt cks d.(declaration_astnum) ->
    ast_num_inc_decl d max ->
    (exists s', eval_decl_with_checks cks' s d s' /\ eval_decl s d s').
Proof.
    intros tb s m d m' tb' cks cks' max h1 h2 h3.
    revert tb' cks cks' max.
    induction h3;
    intros tb' cks cks' max h4 h5 h6 h7.
  - exists (S_Normal ((x, Undefined) :: s)).
    split;
    constructor; auto.
  - inversion h4; subst;
    rewrite <- H0 in H4; inversion H4; subst.
    inversion h5; subst;
    rewrite <- H0 in H; inversion H; subst.
    inversion h7; subst;
    rewrite <- H0 in H7; inversion H7; subst.
    clear H H4 H7.
    specialize (ast_nums_lt_trans _ _ _ h6 H10); intros hz1.
    specialize (well_formed_expr0 _ _ _ _ _ _ _ _ h1 h2 H1 H5 H2 hz1 H8); intros hz2.
    destruct hz2 as [v hz2].
    specialize (eval_expr_with_checks_correct _ _ _ _ _ _ hz2 H2 hz1 H8); intros hz3.
    specialize (eval_expr_state _ _ _ hz3); intros hz4.
    specialize (decl_exists_id d); intros hz5.
    destruct hz5 as [x0 hz5].
    destruct hz4 as [hz4 | hz4].
    + destruct hz4 as [v0 hz4]; rewrite hz4 in *.
      exists (S_Normal ((x0, Value v0) :: s)).
      split.
      * econstructor; auto.
        apply H0. assumption.
      * econstructor; auto.
        apply H0. assumption.
    + rewrite hz4 in *.
      exists S_Run_Time_Error.
      split.
      * econstructor.
        apply H0.
        assumption.
      * econstructor.
        apply H0.
        assumption.
Qed.

Lemma well_formed_decls: forall tl s d tb m m' tb' cks cks' max,
    type_check_store tb s ->
    mode_mapping tb s m -> (* m: a map from variable to its initialization state and in/out mode *)
    well_defined_decls m (d :: tl) m' ->
    well_typed_decls tb (d :: tl) tb' ->
    well_checked_decls cks (d :: tl) cks' ->
    ast_nums_lt cks d.(declaration_astnum) ->
    ast_num_inc_decls (d :: tl) max ->
    (exists s', eval_decls_with_checks cks' s (d :: tl) s' /\ 
                eval_decls s (d :: tl) s'
    ).
Proof.
    induction tl;
    intros s d tb m m' tb' cks cks' max h1 h2 h3 h4 h5 h6 h7;
    inversion h3; subst;
    inversion h4; subst;
    inversion h5; subst;
    inversion h7; subst.
  - specialize (well_formed_decl _ _ _ _ _ _ _ _ _ h1 h2 H2 H3 H5 h6 H0); intros hz1.
    destruct hz1 as [s1 hz1]. 
    destruct hz1 as [hc1 hc2].
    inversion H8; subst.
    specialize (eval_decl_state _ _ _ hc2); intros hz1.
    destruct hz1 as [hz1 | hz1].
    + destruct hz1 as [v hz1].
      rewrite hz1 in *.
      exists (S_Normal v); split.
      econstructor.
        apply hc1. constructor.
      econstructor.
        apply hc2. constructor.
    + rewrite hz1 in *.
      exists S_Run_Time_Error; split;
      constructor; auto.
  - assert (hz0: ast_nums_lt ls'0 (declaration_astnum a)).
        specialize (lt_trans_decl _ _ _ _ _ H5 h6 H7 H10); auto.
    specialize (well_formed_decl _ _ _ _ _ _ _ _ _ h1 h2 H2 H3 H5 h6 H7); intros hz1.
    destruct hz1 as [s' hz1].
    destruct hz1 as [hc1 hc2].
    assert (hz1: eval_decl_with_checks cks' s d s').
      specialize (subset_decls _ _ _ _ _ H8 hz0 H11); intros ha1.
      assert (ha2 :n1 + 1 <= declaration_astnum a); intuition.
      specialize (subset_close_le _ _ _ _ ha1 ha2); intros ha3.
      specialize (eval_decl_with_checks_fixed _ _ _ _ _ _ _ hc1 ha3 H5 h6 H7); auto.
    specialize (eval_decl_state _ _ _ hc2); intros hz2.
    destruct hz2 as [hz2 | hz2].
    + destruct hz2 as [s'1 hz2].
      rewrite hz2 in *.
      specialize (typed_store_reserve_decl _ _ _ _ _ h1 H3 hc2); intros hz3.
      specialize (mode_mapping_consis_decl _ _ _ _ _ _ _ h1 h2 H3 H2 hc2); intros hz4.      
      specialize (IHtl _ _ _ _ _ _ _ _ _ hz3 hz4 H4 H6 H8 hz0 H11).
      destruct IHtl as [s1 H].
      destruct H as [H'1 H'2].
      exists s1.
      split.
      * econstructor.
        apply hz1. assumption.
      * econstructor.
        apply hc2. assumption.
    + rewrite hz2 in *.
      exists S_Run_Time_Error.
      split;
      econstructor; auto.
Qed.

Lemma well_formed_proc_body: forall tb s m f m' cks cks' max k,
    type_check_store tb s ->
    mode_mapping tb s m -> (* m: a map from variable to its initialization state and in/out mode *)
    well_defined_proc_body m f m' ->
    well_typed_proc_body tb f ->
    well_checked_proc_body cks f cks' ->
    ast_nums_lt cks f.(procedure_astnum) ->
    ast_num_inc_proc_body f max ->
    (exists s', eval_proc_body_with_checks cks' s f s' /\ 
                eval_proc s f s') \/ 
    f_eval_proc k s f = S_Unterminated.
Proof.
    intros tb s m f m' cks cks' max k h1 h2 h3.
    revert cks cks' max k.
    induction h3;
    intros cks cks' max k h4 h5 h6 h7;
    inversion h4; subst;
    inversion h5; subst;
    inversion h7; subst.
  - rewrite <- H5 in *.
    inversion H; subst.
    inversion H1; subst.
    inversion H3; subst.
    specialize (ast_nums_lt_trans _ _ _ h6 H7); intros hz1.
    specialize (well_formed_stmt _ _ _ _ _ _ _ _ k h1 h2 H0 H2 H4 hz1 H6); intros hz2.
    destruct hz2 as [hz2 | hz2].
    + destruct hz2 as [s' [hc1 hc2]].
      left. exists s'.
      split.
      * econstructor.
        rewrite <- H5. 
        instantiate (1 := s). constructor.
        assumption.
      * econstructor.
        rewrite <- H5.
        instantiate (1 := s). constructor.
        assumption.
    + right.
      unfold f_eval_proc. 
      rewrite <- H5; simpl.
      assumption.
  - rewrite <- H5 in *.
    specialize (ast_nums_lt_trans _ _ _ h6 H8); intros hz1.
    specialize (lt_trans_decls _ _ _ _ _ _ H3 hz1 H6 H10); intros hz2.
    specialize (well_formed_decls _ _ _ _ _ _ _ _ _ _ h1 h2 H H1 H3 hz1 H6); intros hz3.
    destruct hz3 as [s' [hc1 hc2]].
    assert (hz4: eval_decls_with_checks cks' s (d :: tl) s').
      assert(ha1: subset (max1 + 1) ls2 cks').
        specialize (subset_stmt _ _ _ _ H4 hz2 H7); intros ha'1.
        assert(ha'2: max1 + 1 <= get_ast_num_stmt (procedure_statements f)); intuition.
        specialize (subset_close_le _ _ _ _ ha'1 ha'2); auto.
      specialize (eval_decls_with_checks_fixed _ _ _ _ _ _ _ _ hc1 ha1 H3 hz1 H6); auto.
    specialize (eval_decls_state _ _ _ _ hc2); intros hz5.
    destruct hz5 as [hz5 | hz5].
    + destruct hz5 as [s'1 hz5].
      rewrite hz5 in *.
      specialize (typed_store_reserve_decls _ _ _ _ _ _ h1 H1 hc2); intros hz6.
      specialize (mode_mapping_consis_decls _ _ _ _ _ _ _ _ h1 h2 H1 H hc2); intros hz7.
      specialize (well_formed_stmt _ _ _ _ _ _ _ _ k hz6 hz7 H0 H2 H4 hz2 H7); intros hz8.
      destruct hz8 as [hz8 | hz8].
      * destruct hz8 as [s1 [hc3 hc4]].
        left; exists s1; split.
        econstructor. 
          rewrite <- H5; apply hz4. assumption.
        econstructor.
          rewrite <- H5; apply hc2. assumption.
      * right.
        unfold f_eval_proc.
        rewrite <- H5.
        specialize (f_eval_decls_complete _ _ _ hc2); intros hz9.
        rewrite hz9; simpl; auto.
    + rewrite hz5 in *.
      left; exists S_Run_Time_Error.
      split; constructor;
      rewrite <- H5; auto.
Qed.


(** well-formed terminated program should be always correct with respect 
    to its reference semantics, in other words, for any well-formed 
    terminated subprogram evaluated under two semantics environments 
    "eval_subprogram_with_checks"  and "eval_subprogram", if they 
    start with the same initial state s, they should terminate in 
    the same state s';
    "eval_subprogram_with_checks" is the semantics for subprogram 
    with run time check flags as its passed in parameters;
    "eval_subprogram" is the reference semantics where checks are 
    always performed according to the checking rules;
*)
Theorem well_formed_subprogram: forall tb s m ast_num f m' cks cks' max k,
    type_check_store tb s ->
    mode_mapping tb s m -> (* m: a map from variable to its initialization state and in/out mode *)
    well_defined_subprogram m (Procedure ast_num f) m' ->
    well_typed_subprogram tb (Procedure ast_num f) ->
    well_checked_subprogram cks (Procedure ast_num f) cks' ->
    ast_nums_lt cks ast_num ->
    ast_num_inc_subprogram (Procedure ast_num f) max ->
    (exists s', eval_subprogram_with_checks cks' s (Procedure ast_num f) s' /\ 
                eval_subprogram s (Procedure ast_num f) s') \/ 
    f_eval_subprogram k s (Procedure ast_num f) = S_Unterminated.
Proof.
    intros.
    inversion H1; subst.
    inversion H2; subst.
    inversion H3; subst.
    inversion H5; subst.
    specialize (ast_nums_lt_trans _ _ _ H4 H9); intros hz1.
    specialize (well_formed_proc_body _ _ _ _ _ _ _ _ k H H0 H10 H8 H12 hz1 H13); intros hz2.
    destruct hz2 as [hz2 | hz2].
  - destruct hz2 as [s' [hc1 hc2]].
    left; exists s'; split;
    constructor; auto.
  - right.
    simpl; assumption.
Qed.


