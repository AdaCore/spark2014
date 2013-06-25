Require Export util.
Require Export wellformed.

Inductive type_check_stack: symtb -> stack -> Prop :=
    | TC_Empty: type_check_stack nil nil
    | TC_Bool: forall tb s x m b,
          type_check_stack tb s ->
          type_check_stack ((x, (m, Tbool)) :: tb) ((x, (Value (Bool b))) :: s)
    | TC_Int: forall tb s x m v,
          type_check_stack tb s ->
          type_check_stack ((x, (m, Tint)) :: tb) ((x, (Value (Int v))) :: s)
    | TC_UndefBool: forall tb s x m,
          type_check_stack tb s ->
          type_check_stack ((x, (m, Tbool)) :: tb) ((x, Vundef) :: s)
    | TC_UndefInt: forall tb s x m,
          type_check_stack tb s ->
          type_check_stack ((x, (m, Tint)) :: tb) ((x, Vundef) :: s).

(*
Inductive symbol_consistent: stack -> symtb -> Prop :=
    | SymCons: forall (s: stack) (tb: symtb), 
        ( forall x v, Some v = fetch x s -> 
                          (exists t, stored_value_type (Value v) t /\ ( exists m, lookup x tb = Some (m, t)))) -> 
        (forall x m t, lookup x tb = Some (m, t) -> 
                          reside x s = true /\ 
                          (forall v, (Some v = fetch x s) -> stored_value_type (Value v) t)) -> 
        symbol_consistent s tb.
*)

Lemma typed_value: forall tb s x v,
    type_check_stack tb s ->
    fetch x s = Some v ->
    (exists t, stored_value_type (Value v) t /\ ( exists m, lookup x tb = Some (m, t))).
Proof.
    intros tb s x v h1 h2.
    destruct v.
  - exists Tint.
    split.
    + constructor.
    + induction h1;
       [inversion h2 | | | | ];
       unfold fetch in h2;
       unfold lookup;
       destruct (beq_nat x x0);
       [ inversion h2 | | exists m; auto | | inversion h2 | | inversion h2 | ];
       fold fetch in h2;
       fold lookup;
       specialize (IHh1 h2);
       assumption.
  - exists Tbool.
    split.
    + constructor.
    + induction h1;
       [inversion h2 | | | | ];
       unfold fetch in h2;
       unfold lookup;
       destruct (beq_nat x x0);
       [ exists m; auto | | inversion h2 | | inversion h2 | | inversion h2 | ];
       fold fetch in h2;
       fold lookup;
       specialize (IHh1 h2);
       assumption.
Qed.

Ltac tv_l1 f1 f2 h1 h2 x x0 := 
    unfold f1 in h1;
    unfold f2;
    destruct (beq_nat x x0);
    [ auto |
      fold f1 in h1;
      fold f2;
      specialize (h2 h1);
      rm_exists; auto
    ].

Ltac tv_l2 f1 f2 h1 h2 x x0 tac :=
    unfold f1 in h1;
    unfold f2;
    destruct (beq_nat x x0);
    [ intros; 
      inversion h1; subst;
      inversion H; subst; 
      tac |
      fold f1 in h1;
      fold f2;
      specialize (h2 h1);
      rm_exists; auto
    ].

Lemma typed_value': forall tb s x m t,
    type_check_stack tb s ->
    lookup x tb = Some (m, t) -> 
    reside x s = true /\ 
    (forall v, (Some v = fetch x s) -> stored_value_type (Value v) t).
Proof.
    intros tb s x m t h1 h2.
    induction h1;
    [inversion h2 | | | | ];
    split;
    [ | tv_l2 lookup fetch h2 IHh1 x x0 constructor |
      | tv_l2 lookup fetch h2 IHh1 x x0 constructor |
      | tv_l2 lookup fetch h2 IHh1 x x0 auto |
      | tv_l2 lookup fetch h2 IHh1 x x0 auto
    ];
    tv_l1 lookup reside h2 IHh1 x x0.
Qed.

Inductive symbol_consistent1: stack -> symtb -> Prop :=
    | SymCons: forall (s: stack) (tb: symtb), 
        ( forall x v, Some v = fetch x s -> 
                          (exists t, stored_value_type (Value v) t /\ ( exists m, lookup x tb = Some (m, t)))) -> 
        (forall x m t, lookup x tb = Some (m, t) -> 
                          reside x s = true /\ 
                          (forall v, (Some v = fetch x s) -> stored_value_type (Value v) t)) -> 
        symbol_consistent1 s tb.


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

Lemma well_formed_expr: forall tb s e t,
    type_check_stack tb s -> 
    well_defined_expr s e ->
    well_typed_expr tb e t ->
    exists v, eval_expr s e v /\ return_value_type v t.
Proof.
    intros tb s e t h1 h2.
    generalize t. 
    induction h2; 
    intros t0 h3.
    (* 1. Econst *)
  - exists (ValNormal (Int n)).
    split.
    + constructor. 
       unfold eval_constant; simpl; auto.
    + inversion h3; subst.
       constructor.
  - exists (ValNormal (Bool b)).
    split.
    + constructor. 
       unfold eval_constant; simpl; auto.
    + inversion h3; subst.
       constructor.
    (* 2. Evar *)
  - exists (ValNormal v).
    assert (HZ1: eval_expr s (Evar ast_id x) (ValNormal v)). (* this one is used to prove "return_value_type _ _" *)
    constructor; assumption.
    split.
    + assumption.
    + apply eval_type_reserve with (s := s) (tb := tb) (e := (Evar ast_id x));
       assumption.
    (* 3. Ebinop *)
  - assert (HZ2: exists v, eval_expr s (Ebinop ast_id op e1 e2) v).
    inversion h3; subst. 
    specialize (IHh2_1 h1 _ H5).
    specialize (IHh2_2 h1 _ H6).
    rm_exists.

    destruct x; destruct x0.
    + specialize (binop_rule _ _ _ _ _ _ _ _ _ h1 H1 H0 h3).
       intros h4; rm_exists. 
       exists (ValNormal x); assumption.
    + specialize (exceptionVal_has_no_typ _ _ _ _ h1 H1 H5); intuition.
    + specialize (exceptionVal_has_no_typ _ _ _ _ h1 H0 H6); intuition.
    + specialize (exceptionVal_has_no_typ _ _ _ _ h1 H0 H6); intuition.
    
    + rm_exists. 
       exists x. 
       split; try assumption.
       apply eval_type_reserve with (s := s) (tb := tb) (e := (Ebinop ast_id op e1 e2));
       assumption.
    (* 4. Eunop *)
  - assert(HZ3: exists v, eval_expr s (Eunop ast_id op e) v ).
    inversion h3; subst.
    specialize (IHh2 h1 _ H3).
    rm_exists.
    specialize (eval_type_reserve _ _ _ _ _ h1 H0 H3).
    intros h5.
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


Lemma well_formed_expr_lm: forall tb s e t,
    type_check_stack tb s -> 
    well_defined_expr s e ->
    well_typed_expr tb e t ->
    exists v, eval_expr s e v.
Proof.
    intros tb s e t h1 h2.
    generalize t. 
    induction h2; 
    intros t0 h3.
    (* 1. Econst *)
  - exists (ValNormal (Int n)).
    constructor. unfold eval_constant; simpl; auto.
  - exists (ValNormal (Bool b)).
    constructor. unfold eval_constant; simpl; auto.
    (* 2. Evar *)
  - exists (ValNormal v).
    constructor; assumption.
    (* 3. Ebinop *)
  - inversion h3; subst. 
    specialize (IHh2_1 h1 _ H5).
    specialize (IHh2_2 h1 _ H6).
    rm_exists.

    destruct x; destruct x0.
    + specialize (binop_rule _ _ _ _ _ _ _ _ _ h1 H0 H h3).
       intros h4; rm_exists. 
       exists (ValNormal x); assumption.
    + specialize (exceptionVal_has_no_typ _ _ _ _ h1 H0 H5); intuition.
    + specialize (exceptionVal_has_no_typ _ _ _ _ h1 H H6); intuition.
    + specialize (exceptionVal_has_no_typ _ _ _ _ h1 H H6); intuition.

    (* 4. Eunop *)
  - inversion h3; subst.
    specialize (IHh2 h1 _ H3).
    rm_exists.
    specialize (eval_type_reserve _ _ _ _ _ h1 H H3).
    intros h5.
    destruct x; try rm_contradict.
    destruct v; try rm_contradict.
    set (y :=  (eval_unop op (ValNormal (Bool b)))).
    exists y. 
    econstructor. 
    apply H. intuition.
Qed.

(*
Lemma well_formed_expr_lm: forall tb s e t,
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
      specialize (eval_type_reserve _ _ _ _ _ H1 H4 H8); intros.
      specialize (eval_type_reserve _ _ _ _ _ H1 H6 H9); intros.
      inversion H7; subst. 
      inversion H12.
    * (* 3.3 ValBool, ValInt *)
      inversion H2. inversion H3.
      specialize (eval_type_reserve _ _ _ _ _ H1 H4 H8); intros.
      specialize (eval_type_reserve _ _ _ _ _ H1 H6 H9); intros.
      inversion H7; subst. inversion H12.
    * (* 3.4 ValBool, ValBool *)
      inversion H2. inversion H3.
      specialize (binop_rule _ _ _ _ _ _ _ _ _ H1 H4 H6 H).
      intros h2. inversion h2. destruct x1 as [x2 | x3]. 
      left; exists x2; assumption.
      right; exists x3; assumption.
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

Theorem well_formed_expr: forall tb s e t,
    well_typed_expr tb e t ->
    well_defined_expr s e ->
    symbol_consistent s tb -> 
    exists v, eval_expr s e v /\ return_value_type v t.
Proof.
    intros tb s e t h1 h2 h3.
    specialize (well_formed_expr_lm _ _ _ _ h1 h2 h3).
    intros h.
    rm_or_hyp; rm_exists.
  - exists (ValNormal (Int x)).
    split.
    + assumption.
    + apply eval_type_reserve with (s := s) (tb := tb) (e := e);
       assumption.
  - exists (ValNormal (Bool x)).
    split.
    + assumption.
    + apply eval_type_reserve with (s := s) (tb := tb) (e := e);
       assumption.
Qed.
*)

(* = = = = = = = = = = = = = = =  *)
(* = = = = = = = = = = = = = = =  *)

(* -> *)
Lemma equal_wd_expr_expr2_R: forall s istate e,  
    initializationMap s istate ->
    well_defined_expr s e -> 
    well_defined_expr2 istate e. (* !!! *)
Proof.
    intros s istate e h1 h2.
    induction h2; try constructor; try intuition. 
  - apply initializationMap_consistent1 with (s:=s) (v:=v);
    assumption.
Qed.

(* <- *)    
Lemma equal_wd_expr_expr2_L: forall s istate e,
    initializationMap s istate ->
    well_defined_expr2 istate e -> 
    well_defined_expr s e. (* !!! *)
Proof.
    intros s istate e h1 h2.
    induction h2; try constructor; try intuition.
  - specialize (initializationMap_consistent2 _ _ _ h1 H); intros h3.
    rm_exists.
    apply WD_Evar with (v:=x0).
    auto. 
Qed.

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
(*
Axiom istate_preserve: forall istate e c istate',
    well_defined_expr2 istate e ->
    well_defined_stmt2 istate c istate' ->
    well_defined_expr2 istate' e.
*)

Lemma initializationMap_expr: forall istate1 e istate2,
     well_defined_expr2 istate1 e ->   
     (forall x, fetch2 x istate1 = Some Init -> fetch2 x istate2 = Some Init) ->
     well_defined_expr2 istate2 e.
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
     well_defined_expr2 istate1 e ->   
     (forall x, (fetch2 x istate1 = Some Init -> fetch2 x istate2 = Some Init) /\
                   (fetch2 x istate1 = Some Uninit -> exists m, fetch2 x istate2 = Some m)) ->
     well_defined_expr2 istate2 e.
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
    well_defined_stmt2 istate1 c istate1' ->
    well_defined_stmt2 istate2 c istate2' ->
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
     well_defined_stmt2 istate1 c istate1' ->   
     (forall x, (fetch2 x istate1 = Some Init -> fetch2 x istate2 = Some Init) /\
                   (fetch2 x istate1 = Some Uninit -> exists m, fetch2 x istate2 = Some m)) ->
     exists istate2', well_defined_stmt2 istate2 c istate2'.
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
       apply WD_Sseq2 with (s' := x);
       assumption.
  - exists istate2.
    specialize (IHh1 _ h2).
    rm_exists.
    apply WD_Sifthen2 with (s' := x).    
    + distr_qualifier.
       specialize (initializationMap_expr _ _ _ H H2); intros hz1.
       assumption.
    + assumption.
  - exists istate2.
    specialize (IHh1 _ h2).
    rm_exists.
    apply WD_Swhile2 with (s' := x).
    + distr_qualifier.
       specialize (initializationMap_expr _ _ _ H H2); intros hz1.
       assumption.
    + assumption.
Qed.


Lemma initializationMap_inc: forall istate c istate',
     well_defined_stmt2 istate c istate' ->   
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
     well_defined_stmt2 istate c istate' -> 
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
    assert (hz2: exists istate, well_defined_stmt2 x c2 istate).
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
    assert (hz2': exists istate, well_defined_stmt2 x (Swhile ast_id b c) istate).
    exists x.
    assert (hz3: exists istate, well_defined_stmt2 x c istate).
    specialize (initializationMap_stmt _ _ _ _ H6 hz2); intros hz3.
    inversion hz3.
    specialize (initializationMap_stmt _ _ _ _ H1 IHh1_1); intros hz4.    
    assumption.
    inversion hz3.
    apply WD_Swhile2 with (s' := x0). 
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
     well_defined_stmt2 istate c1 istate' -> 
     well_defined_stmt2 istate' c2 istate'' ->      
     initializationMap s' istate1 ->
     exists istate2, well_defined_stmt2 istate1 c2 istate2.
Proof.
    intros s istate c1 s' istate' c2 istate'' istate1 h1 h2 h3 h4 h5.
    specialize (eval_stmt_greater _ _ _ _ _ _ h2 h1 h3 h5); intros hz1.
    specialize (initializationMap_stmt _ _ _ _ h4 hz1); intros hz2.
    assumption.
Qed.


(*
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

Axiom while_well_form : forall s tb b k c s' ast_id,
    symbol_consistent s tb ->
    well_defined_expr s b -> 
    well_typed_expr tb b Tbool ->
    f_eval_stmt k s c = SNormal s' ->
        (exists s'0 : stack, f_eval_stmt k s' (Swhile ast_id b c) = SNormal s'0) \/
        f_eval_stmt k s' (Swhile ast_id b c) = SUnterminated.

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
*)


Ltac unfold_f_eval_stmt :=
    match goal with
    | [ |- context[f_eval_stmt ?k ?s _]] => unfold f_eval_stmt; simpl
    end.

(*
Ltac invert_well_form_hyp :=
    match goal with 
    | [h: well_defined_stmt2 _ (Sassign _ ?x ?e) _ |- _] => inversion h; subst
    | [h: well_typed_stmt _ (Sassign _ ?x ?e) |- _] => inversion h; subst
    | [h: well_defined_stmt2 _ (Sifthen _ ?b ?c) _ |- _] => inversion h; subst
    | [h: well_typed_stmt _ (Sifthen _ ?b ?c) |- _] => inversion h; subst
    | [h: well_defined_stmt2 _ (Swhile _ ?b ?c) _ |- _] => inversion h; subst
    | [h: well_typed_stmt _ (Swhile _ ?b ?c) |- _] => inversion h; subst
    end.
*)

(* Lemmas to prove... *)
Lemma well_formed_cmd: forall tb c s istate istate' k, 
    well_typed_stmt tb c -> (* we want to do induction on 'c', but keep the variables 's', 'istate' ... universal *)
    type_check_stack tb s ->
    initializationMap s istate ->
    well_defined_stmt2 istate c istate' ->
    (exists s', f_eval_stmt k s c = (SNormal s')) \/ f_eval_stmt k s c = SUnterminated.
Proof.
    intros tb. 
    (* in the later proof during the induction on 'c', we have to keep the variables 's', 'istate', 'istate'', 'k' 
       universal, that's why in the definition of lemma, we put 'well_typed_stmt' at the beginning  *)
    induction c;
    intros s istate istate' k h1 h2 h3 h4.
  - (* 1. Sassign *)
    inversion h1; subst.
    inversion h4; subst.
    specialize (equal_wd_expr_expr2_L _ _ _ h3 H6); intros hz1.
    specialize (well_formed_expr _ _ _ _ h2 hz1 H4); intros hz2.
    rm_exists.
    specialize (f_eval_expr_complete _ _ _ H0); intros hz3.
    unfold_f_eval_stmt.
    destruct k.
    + right; auto.
    + left. rewrite hz3.
       destruct x.
       * specialize (valid_update _ _ _ _ _ v h2 h1); intros hz4.
         rm_exists.
         rewrite H.
         exists x; auto.
       * specialize (exceptionVal_has_no_typ _ _ _ _ h2 H0 H4); intros hz5.
         intuition.
  - (* 2. Sifthen *)
    inversion h1; subst.
    inversion h4; subst.
    unfold_f_eval_stmt.
    destruct k.
    + right; auto.
    + fold f_eval_stmt.
       specialize (IHc _ _ _ k H4 h2 h3 H7).
       specialize (equal_wd_expr_expr2_L _ _ _ h3 H6); intros hz1.
       specialize (well_formed_expr _ _ _ _ h2 hz1 H2); intros hz2.
       rm_exists.
       specialize (f_eval_expr_complete _ _ _ H0); intros hz3.
       rewrite hz3.
       destruct x.
       * destruct v.
         rm_contradict.
         destruct b.
           assumption.
           left; exists s; auto.
       * rm_contradict.
  - (* 3. Swhile *)
    inversion h1; subst.
    inversion h4; subst.
    unfold_f_eval_stmt.
    destruct k.
    + right; auto.
    + fold f_eval_stmt.
       specialize (IHc _ _ _ k H4 h2 h3 H7).
       specialize (equal_wd_expr_expr2_L _ _ _ h3 H6); intros hz1.
       specialize (well_formed_expr _ _ _ _ h2 hz1 H2); intros hz2.
       rm_exists.
       specialize (f_eval_expr_complete _ _ _ H0); intros hz3.
       rewrite hz3.
       destruct x.
       * destruct v.
         rm_contradict.
         destruct b.
           inversion IHc.
           rm_exists.
           rewrite H3.
             admit. (******** ?????????? ********)
           rewrite H.
           right; auto.
           left; exists s; auto.
       * rm_contradict.
  - (* 4. Sseq *)
    inversion h1; subst.
    inversion h4; subst.
    unfold_f_eval_stmt.
    destruct k.
    + right; auto.
    + fold f_eval_stmt.
    specialize (IHc1 _ _ _ k H2 h2 h3 H6).
    inversion IHc1.
      * rm_exists.
        rewrite H0.
        remember H0 as H'0. clear HeqH'0.
        apply f_eval_stmt_complete in H0.
        specialize (symbol_consistent_reserve _ _ _ _ h2 H2 H0); intros hz1.
        specialize (imap_exists x); intros hz2; rm_exists.
        specialize (f_eval_stmt_complete _ _ _ _ H'0); intros hz2.
        specialize (initializationMap_consistent _ _ _ _ _ _ _ _ h3 hz2 H6 H7 H); intros hz3.
        rm_exists.
        specialize (IHc2 _ _ _ k H4 hz1 H H1).
        assumption.
     * rewrite H.
       right; auto.
Qed.



