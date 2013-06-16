Require Export util.
Require Export wellformed.

(* TODO *)
(* Right now the following is the assumption, which needs to be proved later. *)

Inductive symbol_consistent: stack -> symtb -> Prop :=
    | SymCons: forall (s: stack) (tb: symtb), 
        ( forall x v, Some v = fetch x s -> 
                          (exists t, stored_value_type (Value v) t /\ ( exists m, lookup x tb = Some (m, t)))) -> 
        (forall x m t, lookup x tb = Some (m, t) -> 
                          reside x s = true /\ 
                          (forall v, (Some v = fetch x s) -> stored_value_type (Value v) t)) -> 
        symbol_consistent s tb.

Axiom eval_type_reserve: 
    forall (s: stack) (tb: symtb) e v t,
    symbol_consistent s tb -> 
    eval_expr s e v ->
    well_typed_expr tb e t ->
    return_value_type v t. 

(* basic lemmas *)
Lemma binop_ind: forall s tb ast_id op e1 e2 v1 v2 t,
    eval_expr s e1 (ValNormal (Int v1)) ->
    eval_expr s e2 (ValNormal (Int v2)) -> 
    well_typed_expr tb (Ebinop ast_id op e1 e2) t -> (* for example, disallow expression: 8 /\ 9 *)
    symbol_consistent s tb -> 
    (exists v : Z, eval_expr s (Ebinop ast_id op e1 e2) (ValNormal (Int v))) \/ 
    (exists b: bool, eval_expr s (Ebinop ast_id op e1 e2) (ValNormal (Bool b))).
Proof.
    intros.
    inversion H1; subst.
    specialize (eval_type_reserve s tb e1 (ValNormal (Int v1)) t0 H2 H H9); intros.
    specialize (eval_type_reserve s tb e2 (ValNormal (Int v2)) t0 H2 H0 H10); intros.
    inversion H3; subst.
    (* destruct on the binary operator *)
    destruct op; simpl;
    (* 1. Oand | Oor *)
    [right | right | inversion H11 | inversion H11 | left | left | left | left];
    [(* 2. Ceq *)
     assert (exists b, ValNormal (Bool b) = eval_binop Ceq (ValNormal (Int v1)) (ValNormal (Int v2))); 
         [simpl_binop; exists (Zeq_bool v1 v2); auto | ] |
     (* 3. Cne *)
     assert (exists b, ValNormal (Bool b) = eval_binop Cne (ValNormal (Int v1)) (ValNormal (Int v2))); 
          [simpl_binop; exists (Zneq_bool v1 v2); auto | ] |
     (* 4. Oadd *)
     assert (exists n, ValNormal (Int n) = eval_binop Oadd (ValNormal (Int v1)) (ValNormal (Int v2))); 
         [simpl_binop; exists (v1 + v2)%Z; auto | ] |
     (* 5. Osub *)
     assert (exists n, ValNormal (Int n) = eval_binop Osub (ValNormal (Int v1)) (ValNormal (Int v2))); 
         [simpl_binop; exists (v1 - v2)%Z; auto | ] |
     (* 6. Oml *)
     assert (exists n, ValNormal (Int n) = eval_binop Omul (ValNormal (Int v1)) (ValNormal (Int v2))); 
         [simpl_binop; exists (v1 * v2)%Z; auto | ] |
     (* 7. Odiv *)
     assert (exists n, ValNormal (Int n) = eval_binop Odiv (ValNormal (Int v1)) (ValNormal (Int v2)));
         [simpl_binop; exists (v1 / v2)%Z; auto | ]
    ];
    inversion H5; exists x;
    rm_eval_expr; unfold good_value; auto.
Qed.

Lemma binop_ind': forall s tb ast_id op e1 e2 v1 v2 t,
    eval_expr s e1 (ValNormal (Bool v1)) ->
    eval_expr s e2 (ValNormal (Bool v2)) -> 
    well_typed_expr tb (Ebinop ast_id op e1 e2) t -> (* for example, disallow expression: 8 and 9 *)
    symbol_consistent s tb -> 
    (exists b: bool, eval_expr s (Ebinop ast_id op e1 e2) (ValNormal (Bool b))).
Proof.
    intros. 
    inversion H1; subst.
    specialize (eval_type_reserve s tb e1 (ValNormal (Bool v1)) t0 H2 H H9). intros.
    specialize (eval_type_reserve s tb e2 (ValNormal (Bool v2)) t0 H2 H0 H10). intros.
    inversion H3; subst.
    assert (exists b, ValNormal (Bool b) = eval_binop op (ValNormal (Bool v1)) (ValNormal (Bool v2))).
    unfold eval_binop. 
    destruct op; simpl; try (inversion H11).
    exists (v1 && v2). auto.
    exists (v1 || v2). auto.
    inversion H5. 
    exists x. 
    rm_eval_expr.
Qed.
    
Theorem well_formed_expr: forall tb s e t,
    well_typed_expr tb e t ->
    well_defined_expr s e ->
    symbol_consistent s tb -> 
    (exists v, eval_expr s e (ValNormal (Int v))) \/ (exists b, eval_expr s e (ValNormal (Bool b))).
Proof.
    intros tb s e.
    induction e; 
    intros t H H0 H1.
  - (* 1. Econst *)
    destruct c.
    * left. 
      exists z. 
      constructor; auto.
    * right. 
      exists b. 
      constructor; auto.
  - (* 2. Evar *)
    inversion H0; subst.
    destruct v as [ n | b].
    * left. 
      exists n.
      rm_eval_expr.
    * right.
      exists b.
      rm_eval_expr.
  - (* 3. Ebinop *)
    inversion H; subst. 
    inversion H0; subst.
    specialize (IHe1 t0  H8 H5 H1).
    specialize (IHe2 t0 H9 H11 H1).
    destruct IHe1; destruct IHe2.
    * (* 3.1 ValInt, ValInt *)
      inversion H2. inversion H3.
      specialize (binop_ind s tb a b e1 e2 x x0 t H4 H6 H H1). 
      intros. apply H7.
    * (* 3.2 ValInt, ValBool *)
      inversion H2. inversion H3.
      specialize (eval_type_reserve s tb e1 (ValNormal (Int x)) t0 H1 H4 H8); intros.
      specialize (eval_type_reserve s tb e2 (ValNormal (Bool x0)) t0 H1 H6 H9); intros.
      inversion H7; subst. inversion H12.
    * (* 3.3 ValBool, ValInt *)
      inversion H2. inversion H3.
      specialize (eval_type_reserve s tb e1 (ValNormal (Bool x)) t0 H1 H4 H8); intros.
      specialize (eval_type_reserve s tb e2 (ValNormal (Int x0)) t0 H1 H6 H9); intros.
      inversion H7; subst. inversion H12.
    * (* 3.4 ValBool, ValBool *)
      inversion H2. inversion H3.
      specialize (binop_ind' s tb a b e1 e2 x x0 t H4 H6 H H1). 
      intros. right; apply H7.
  - (* 4. Eunop *)
    inversion H; subst. 
    inversion H0; subst.
    specialize (IHe Tbool H6 H4 H1). 
    inversion IHe; inversion H2.
    * (* 4.1 ValInt *)
      left. 
      inversion H; subst.
      specialize (eval_type_reserve s tb e (ValNormal (Int x)) Tbool H1 H3 H8); intros. 
      inversion H5.
    * (* 4.2 ValBool *)
      right. 
      assert (exists b, ValNormal (Bool b) = eval_unop u (ValNormal (Bool x))).
      unfold eval_unop. destruct u. simpl. exists (negb x). auto.
      inversion H5; subst. exists x0. 
      eapply eval_Eunop; eassumption.
Qed.

(* -> : this direction doesn't work *)
(*
Theorem well_formed_stmt: forall tb s c,
    well_typed_stmt tb c ->
    well_defined_stmt s c ->
    symbol_consistent s tb -> 
    exists s1, eval_stmt_R s c s1.
*)

(*
Theorem good_expr_props: forall tb s e v n b,
    symbol_consistent s tb /\ eval_expr s e v /\ (v = (ValNormal (Int n)) \/ v = (ValNormal (Bool b))) ->
        (exists t, well_typed_expr tb e t) /\ well_defined_expr s e.
Proof.
    intros tb s.
    induction e; 
    intros v n b0 H;
    destruct H as [h [h1 h2]].
  - (* 1. Econst *)
    split.
    + (* well_typed *)
      destruct c.
      * exists Tint; constructor.
      * exists Tbool; constructor.
    + (* well_defined *)
      rm_wd_expr. 
  - (* 2. Evar *)
    split.
    + (* well_typed *)
       inversion h; subst.
       inversion h2; subst; (* split into two cases: *) 
       inversion h1; subst;
       [specialize (H i (Int n) H3) | 
        specialize (H i (Bool b0) H3)];
       inversion H; clear H. 
       inversion H1. exists x. (* made some modification from here to next '+' *)
       rm_wt_expr. 
       rm_exists.
       exists x; rm_wt_expr.
       inversion H1;
       exists x; rm_wt_expr; 
       intuition.
    + (* well_defined *)
      destruct h2; subst; 
      inversion h1; subst;
      rm_wd_expr.
  - (* 3. Ebinop *)
    split.
    + (* well_typed *)
       inversion h1; subst. 
       inversion h2 as [h3 | h4]; clear h2. (* --> split into two cases: *)
       (* Int case *)
       specialize (expr_type_infer b v1 v2 n h3); intros H1.
       rm_exists.
       subst v1 v2.
       specialize (IHe1 (ValNormal (Int x)) x true).
       intuition.
       specialize (IHe2 (ValNormal (Int x0)) x0 true).
       intuition.
       rm_exists.
       specialize (eval_type_reserve s tb e1 (ValNormal (Int x)) x2 h H5 H0); intros H8.
       specialize (eval_type_reserve s tb e2 (ValNormal (Int x0)) x1 h H6 H3); intros H9.       
       inversion H8; clear H8; subst. inversion H9; clear H9; subst.
       unfold eval_binop in h3. 
       destruct b; try (inversion h3).
           exists Tint; rm_wt_expr. 
           exists Tint; rm_wt_expr.
           exists Tint; rm_wt_expr.
           exists Tint; rm_wt_expr.
       (* Bool case *)
       specialize (expr_type_infer' b v1 v2 b0 h4); intros H1.
       inversion H1; clear H1; 
       rm_exists; subst.
       specialize (IHe1 (ValNormal (Int x)) x true).
       intuition.
       specialize (IHe2 (ValNormal (Int x0)) x0 true).
       intuition.
       rm_exists.
       specialize (eval_type_reserve s tb e1 (ValNormal (Int x)) x2 h H5 H0); intros H8.
       specialize (eval_type_reserve s tb e2 (ValNormal (Int x0)) x1 h H6 H3); intros H9.       
       inversion H8; clear H8; subst. inversion H9; clear H9; subst.
       unfold eval_binop in h4. 
       destruct b; try (inversion h4).
           exists Tbool; rm_wt_expr. 
           exists Tbool; rm_wt_expr.
       (***)
       specialize (IHe1 (ValNormal (Bool x)) 0%Z x).
       intuition.
       specialize (IHe2 (ValNormal (Bool x0)) 0%Z x0).
       intuition.
       rm_exists.
       specialize (eval_type_reserve s tb e1 (ValNormal (Bool x)) x2 h H5 H4); intros H8.
       specialize (eval_type_reserve s tb e2 (ValNormal (Bool x0)) x1 h H6 H3); intros H9.       
       inversion H8; clear H8; subst. inversion H9; clear H9; subst.
       unfold eval_binop in h4. 
       destruct b; try (inversion h4).
           exists Tbool; rm_wt_expr. 
           exists Tbool; rm_wt_expr.
    + (* well_defined *)
       inversion h2; clear h2; subst.
       inversion h1; subst. 
       symmetry in H7.
       specialize (expr_type_infer b v1 v2 n H7); intros H1.
       rm_exists. subst.
       specialize (IHe1 (ValNormal (Int x)) x true).
       intuition.
       specialize (IHe2 (ValNormal (Int x0)) x0 true).
       intuition.
       rm_exists.
       rm_wd_expr.
       (**)
       inversion h1; subst.
       symmetry in H7.
       specialize (expr_type_infer' b v1 v2 b0 H7); intros H1.
       inversion H1.
       rm_exists. subst.
       clear H1.
       specialize (IHe1 (ValNormal (Int x)) x true).
       intuition.
       specialize (IHe2 (ValNormal (Int x0)) x0 true).
       intuition. rm_wd_expr.
       rm_exists. subst.
       clear H1.
       specialize (IHe1 (ValNormal (Bool x)) 0%Z x).
       intuition.
       specialize (IHe2 (ValNormal (Bool x0)) 0%Z x0).
       intuition. rm_wd_expr.
  - (* 4. Eunop *)
    split.
    + (* well_typed *)
       inversion h2; clear h2; subst.
       inversion h1; subst.
       unfold eval_unop in H4; destruct op in H4. 
       inversion H4.
       inversion h1; subst.
       specialize (IHe (ValNormal (Bool b)) 0%Z b).
       intuition.
       rm_exists. 
       specialize (eval_type_reserve s tb e (ValNormal (Bool b)) x h H2 H0); intros H8.
       inversion H8; subst.
       exists Tbool. rm_wt_expr.   
    + (* well_defined *)
       inversion h2 as [h3 | h4]; subst;
       inversion h1; subst. 
       unfold eval_unop in H4; destruct op in H4. 
       inversion H4.
       specialize (IHe (ValNormal (Bool b)) 0%Z b).
       clear h2.
       intuition.
       rm_wd_expr.
Qed.
*)



(* Prove the properties of the terminated program *)
(*
Theorem good_stmt_props: forall tb s s1 c,
    symbol_consistent s tb /\ well_typed_stmt tb c /\ eval_stmt_R s c s1 ->
        well_defined_stmt s c.
Proof.
    intros. inversion H; clear H. inversion H1; clear H1.
    induction c.
    (* 1. Sassign *)
  - inversion H2; subst. 
    eapply WD_Sassign.
    inversion H; subst.
    (* 2. Sifthen *)
 
    (* 3. Swhile *)
  
    (* 4. Sseq *)

    (* 5. Sreturn *)
  
    (* 6. Sassert *)
  
    (* 7. Sloopinvariant *)

*)
