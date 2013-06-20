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

(*
Inductive return_value_type : return_val -> typ -> Prop :=
    EVT_Int : forall n : Z, return_value_type (ValNormal (Int n)) Tint
  | EVT_Bool : forall b : bool, return_value_type (ValNormal (Bool b)) Tbool

Inductive stored_value_type : val -> typ -> Prop :=
    SVT_Int : forall n : Z, stored_value_type (Value (Int n)) Tint
  | SVT_Bool : forall b : bool, stored_value_type (Value (Bool b)) Tbool

*)

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

Lemma eval_type_reserve: 
    forall (s: stack) (tb: symtb) e v t,
    symbol_consistent s tb -> 
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
    inversion h1; subst.
    symmetry in H3.
    specialize (H0 i In t H3).
    rm_exists.
    specialize (H2 _ H8).
    apply value_type_consistent; assumption.
  - (* Ebinop *)
    specialize (IHe1 v1 t0 h1 H14 H5).
    specialize (IHe2 v2 t0 h1 H15 H6).
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
Qed.

(* basic lemmas *)
Ltac br_rm_rop v1 v2 op v1' v2' :=
    match goal with
    | [ |- exists v : value, eval_expr _ (Ebinop ?ast_id ?rop ?e1 ?e2) (ValNormal ?v)] =>
            assert (exists b, ValNormal (Bool b) = eval_binop rop (ValNormal v1) (ValNormal v2))
    end; [ simpl_binop; exists (op v1' v2'); auto | ].

Ltac br_rm_aop v1 v2 v3 :=
    match goal with
    | [ |- exists v : value, eval_expr _ (Ebinop ?ast_id ?aop ?e1 ?e2) (ValNormal ?v)] =>
            assert (exists n, ValNormal (Int n) = eval_binop aop (ValNormal v1) (ValNormal v2))
    end; [ simpl_binop; exists v3; auto | ].

Ltac br_clearer v f :=
    exists v;
    rm_eval_expr; unfold f; auto.   

Lemma binop_rule: forall s tb e1 v1 e2 v2 ast_id op t,
    symbol_consistent s tb -> 
    eval_expr s e1 (ValNormal v1) ->
    eval_expr s e2 (ValNormal v2) -> 
    well_typed_expr tb (Ebinop ast_id op e1 e2) t -> (* for example, disallow expression: 8 /\ 9 *)
    (exists v : value, eval_expr s (Ebinop ast_id op e1 e2) (ValNormal v)).
Proof.    
    intros.
    inversion H2; subst.
    specialize (eval_type_reserve s tb e1 (ValNormal v1) t0 H H0 H9); intros h1.
    specialize (eval_type_reserve s tb e2 (ValNormal v2) t0 H H1 H10); intros h2.    
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
            assert (exists b, ValNormal (Bool b) = eval_unop uop (ValNormal v1)) 
    end; 
    [simpl_unop; exists v2; auto | ].

Ltac ur_clearer v :=
    exists v;
    eapply eval_Eunop; eassumption.   

Lemma unop_rule: forall s tb e v ast_id op t,
    symbol_consistent s tb -> 
    eval_expr s e (ValNormal v) ->
    well_typed_expr tb (Eunop ast_id op e) t -> 
    (exists bv : value, eval_expr s (Eunop ast_id op e) (ValNormal bv)).
Proof.
    intros.
    inversion H1; subst.
    specialize (eval_type_reserve s tb e (ValNormal v) Tbool H H0 H6); 
    intros h1.
    destruct v; try rm_contradict.
    destruct op.
    ru_rm_unop (Bool b) (negb b).
    rm_exists.  
    ur_clearer (Bool x).
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

      specialize (binop_rule s tb e1 (Int x) e2 (Int x0) a b t H1 H4 H6 H).
      intros h1. inversion h1. destruct x1 as [x2 | x3]. 
      left; exists x2; assumption.
      right; exists x3; assumption.

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

      specialize (binop_rule s tb e1 (Bool x) e2 (Bool x0) a b t H1 H4 H6 H).
      intros h2. inversion h2. destruct x1 as [x2 | x3]. 
      left; exists x2; assumption.
      right; exists x3; assumption.
(*      
      specialize (binop_ind' s tb a b e1 e2 x x0 t H4 H6 H H1). 
      intros. right; apply H7.
*)
  - (* 4. Eunop *)
    inversion H; subst. 
    inversion H0; subst.
    specialize (IHe Tbool H6 H4 H1). 
    inversion IHe; rm_exists.    
    + specialize (eval_type_reserve s tb e (ValNormal (Int x)) Tbool H1 H3 H6); 
       intros h3; 
       inversion h3. 
    + specialize (unop_rule s tb e (Bool x) a u Tbool H1 H3 H); 
       intros h4; inversion h4. 
       destruct x0 as [x2 | x3]. 
       left; exists x2; assumption.
       right; exists x3; assumption.
Qed.

(* = = = = = = = = = = = = = = =  *)
(* = = = = = = = = = = = = = = =  *)

Axiom valid_update: forall s tb ast_id x e v,
    symbol_consistent s tb ->
    well_typed_stmt tb (Sassign ast_id x e) ->
    exists s', update s x (Value v) = Some s'.

(* -> *)
Axiom equal_wd_expr_expr2_R: forall s istate e,  
    initializationMap s istate ->
    well_defined_expr s e -> 
    well_defined_expr2 istate e.

(* <- *)    
Axiom equal_wd_expr_expr2_L: forall s istate e,
    initializationMap s istate ->
    well_defined_expr2 istate e -> 
    well_defined_expr s e.

Axiom symbol_consistent_reserve: forall s tb k c s',
     symbol_consistent s tb -> 
     f_eval_stmt k s c = SNormal s' -> 
     symbol_consistent s' tb.

Axiom imap_exists: forall s, exists istate, 
    initializationMap s istate.

Axiom initializationMap_consistent: forall (s: stack) istate k s c1 s' istate' c2 istate'' istate1,
     initializationMap s istate ->
     f_eval_stmt k s c1 = SNormal s' -> 
     well_defined_stmt2 istate c1 istate' -> 
     well_defined_stmt2 istate' c2 istate'' ->      
     initializationMap s' istate1 ->
     exists istate2, well_defined_stmt2 istate1 c2 istate2. 

Axiom type_consistent: forall s tb b v, 
    symbol_consistent s tb ->
    well_typed_expr tb b Tbool ->
    ~eval_expr s b (ValNormal (Int v)).  

Axiom initializationMap_Expr: forall (s: stack) istate e k c s' istate',
    initializationMap s istate ->
    well_defined_expr2 istate e ->
    f_eval_stmt k s c = SNormal s' ->
    initializationMap s' istate' ->
    well_defined_expr2 istate' e.

Axiom initializationMap_Stmt: forall (s: stack) istate k c s' istate' istate1,
    initializationMap s istate ->
    f_eval_stmt k s c = SNormal s' ->
    well_defined_stmt2 istate c istate' ->
    initializationMap s' istate1 ->
    exists istate2, well_defined_stmt2 istate1 c istate2.


(* Lemmas to prove... *)
Lemma well_formed_cmd: forall k s tb c istate istate', 
    symbol_consistent s tb ->
    initializationMap s istate ->
    well_typed_stmt tb c ->
    well_defined_stmt2 istate c istate' ->
    (exists s', f_eval_stmt k s c = (SNormal s')) \/ f_eval_stmt k s c = SUnterminated.
Proof.
    intros k s tb c. 
    functional induction (f_eval_stmt k s c);
    intros istate istate' h1 h2 h3 h4;
    try intuition.
  - left.
    exists s1. auto.
  - left. 
    (**)specialize (valid_update s tb ast_id x e0 v h1 h3). intros h5.
    inversion h5; subst.
    rewrite e3 in H. inversion H.
  - inversion h4; subst.
    inversion h3; subst.
    (**)specialize (equal_wd_expr_expr2_L s istate e0 h2 H4). intros h6.
    specialize (well_formed_expr tb s e0 t H6 h6 h1). intros.
    inversion H; inversion H0.
    + specialize (f_eval_expr_complete s e0 (ValNormal (Int x0)) H1). intros h7.
       rewrite e2 in h7. inversion h7.
    + specialize (f_eval_expr_complete s e0 (ValNormal (Bool x0)) H1). intros h7.
       rewrite e2 in h7. inversion h7.
  - (* Cseq *) 
    inversion h3; subst.
    inversion h4; subst.
    specialize (IHs0 istate s' h1 h2 H2 H6).
    (**)specialize (symbol_consistent_reserve s tb k' c1 s1 h1 e1). intros h8.
    specialize (imap_exists s1). intros h9. inversion h9; clear h9.

    (**)specialize (initializationMap_consistent s istate k' s c1 s1 s' c2 istate' x h2 e1 H6 H7 H). intros h9.
    inversion h9.    
    specialize (IHs1 x x0 h8 H H4 H0). assumption.    
    
  - inversion h3; subst. inversion h4; subst.
    specialize (IHs0 istate s' h1 h2 H2 H6).
    inversion IHs0.
    + inversion H. rewrite e1 in H0; inversion H0.
    + rewrite e1 in H; inversion H.
  - (* Cifthen *)
    inversion h3; subst.
    inversion h4; subst.
    specialize (IHs0 istate' s' h1 h2 H4 H7). assumption.
  - left. exists s; auto.  
  - inversion h3; subst.
    inversion h4; subst.
    (**)specialize (equal_wd_expr_expr2_L s istate' b h2 H6). intros h6.
    (**)specialize (well_formed_expr tb s b Tbool H2 h6 h1). intros h7.
    inversion h7.
    + inversion H.
       specialize (type_consistent s tb b x h1 H2). intros h8.
       intuition.
    + inversion H.
       apply f_eval_expr_complete in H0. 
       rewrite H0 in y.
       destruct x in y; intuition.
  - (* Swhile *)
    inversion h3; subst.
    inversion h4; subst.
    specialize (IHs0 istate' s' h1 h2 H4 H7).
    (**)specialize (symbol_consistent_reserve s tb k' c0 s1 h1 e2). intros h8.
    specialize (imap_exists s1). intros h9. inversion h9; clear h9.
    
    assert(well_defined_stmt2 x (Swhile ast_id b c0) x).
    (**)specialize (initializationMap_Expr s istate' b k' c0 s1 x   h2 H6 e2 H). intros h9.
    assert(exists y, well_defined_stmt2 x c0 y).
    (**)specialize (initializationMap_Stmt s istate' k' c0 s1 s' x h2 e2 H7 H). intros h10.
    inversion h10; clear h10.
    exists x0; assumption.
    inversion H0.
    apply WD_Swhile2 with (s' := x0); assumption.
    
    specialize (IHs1 x x h8 H h3 H0).
    assumption.
  - inversion h3; subst.
    inversion h4; subst.
    specialize (IHs0 istate' s' h1 h2 H4 H7). 
    inversion IHs0.
    + inversion H. rewrite e2 in H0; inversion H0.
    + rewrite e2 in H; inversion H.
  - left. exists s; auto.
  -  inversion h3; subst.
    inversion h4; subst.
    (**)specialize (equal_wd_expr_expr2_L s istate' b h2 H6). intros h6.
    (**)specialize (well_formed_expr tb s b Tbool H2 h6 h1). intros h7.
    inversion h7.
    + inversion H.
       specialize (type_consistent s tb b x h1 H2). intros h8.
       intuition.
    + inversion H.
       apply f_eval_expr_complete in H0. 
       rewrite H0 in y.
       destruct x in y; intuition.



