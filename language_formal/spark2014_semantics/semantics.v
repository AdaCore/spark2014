Require Export values.
Require Export environment.
Require Import util.

(** * Relational Semantics *)
Definition eval_constant (cst: constant): return_val :=
    match cst with
    | Ointconst v => ValNormal (Int v)
    | Oboolconst b => ValNormal (Bool b)
    end.

(* 
   - Use type checker to make sure that operator works on the operand of right type
   - There still exists problems like overflow or division by zero in the binary operation
 *)
Definition eval_binop (op: binary_operation) (v1: return_val) (v2: return_val): return_val :=
    match op with
    | Ceq => Val.eq v1 v2
    | Cne => Val.ne v1 v2
    | Oand => Val.and v1 v2
    | Oor => Val.or v1 v2
    | Oadd => Val.add v1 v2
    | Osub => Val.sub v1 v2
    | Omul => Val.mul v1 v2
    | Odiv => Val.div v1 v2
    end.

Definition eval_unop (op: unary_operation) (v: return_val): return_val :=
    match op with
    | Onot => Val.not v
    end.

(* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - *)
    
(** ** Run-Time Checking Rules *)

(** *** check actions *)
(** which are needed to be performed before excecuting the program *)
Inductive check_action: Type := 
   | Division_Check: expr -> check_action
   | Overflow_Check: expr -> check_action
   | No_Check: check_action.

(** *** semantics for check actions *)
Inductive is_not_zero: Z -> bool -> Prop :=
    | Not_Zero: forall v, v <> 0%Z -> is_not_zero v true
    | Is_Zero: forall v, v = 0%Z -> is_not_zero v false.

Definition Interpreter_Expr: Type := stack -> expr -> return_val -> Prop.

Inductive do_check (IE: Interpreter_Expr): stack -> check_action -> bool -> Prop :=
    | DC_Division_By_Zero: forall s e1 v1 e2 v2 b ast_id,
        IE s e1 (ValNormal (Int v1)) -> (* make sure that v1 and v2 are type consistent *)
        IE s e2 (ValNormal (Int v2)) ->
        is_not_zero v2 b ->
        do_check IE s (Division_Check (Ebinop ast_id Odiv e1 e2)) b
    | DC_No_Check: forall s,
        do_check IE s No_Check true.
(*
    | DC_Overflow: 
    | DC_Range: 
    | ... 
*)

(** *** check rules marking what and where to check *)
(** 
      - Do_Division_Check
       
       This flag is set on a division operator (/ mod rem) to indicate
       that a zero divide check is required. 

     - Do_Overflow_Check

       This flag is set on an operator where an overflow check is required on
       the operation. This flag is also set on if and case expression nodes if 
       we are operating in either MINIMIZED or ELIMINATED overflow checking 
       mode (to make sure that we properly process overflow checking for dependent 
       expressions).
*)

Inductive check_flag: expr -> check_action -> Prop :=
    | CF_Econst_Int: forall ast_id n,
        check_flag (Econst ast_id (Ointconst n)) No_Check
    | CF_Econst_Bool: forall ast_id b,
        check_flag (Econst ast_id (Oboolconst b)) No_Check
    | CF_Evar: forall ast_id x,  
        check_flag (Evar ast_id x) No_Check
    | CF_Ebinop_Div: forall ast_id e1 e2,
        check_flag (Ebinop ast_id Odiv e1 e2) (Division_Check (Ebinop ast_id Odiv e1 e2))
    | CF_Ebinop_Others: forall ast_id op e1 e2,
        op <> Odiv ->
        check_flag (Ebinop ast_id op e1 e2) No_Check
    | CF_Eunop: forall ast_id op e,
        check_flag (Eunop ast_id op e) No_Check.

(** *** checking procedure *)
Inductive run_time_check (IE: Interpreter_Expr):  stack -> expr -> bool -> Prop :=
    | RTC: forall e runtime_check b s,
        check_flag e runtime_check ->
        do_check IE s runtime_check b ->
        run_time_check IE s e b.

(** ** Expression semantics *)
Inductive eval_expr: stack -> expr -> return_val -> Prop :=
    | eval_Econst: forall cst v s ast_id,
        eval_constant cst = v ->
        eval_expr s (Econst ast_id cst) v
    | eval_Evar: forall x s v ast_id,
        fetch x s = Some v ->
        eval_expr s (Evar ast_id x) (ValNormal v)
    | eval_Ebinop1: forall s e1 ast_id op e2,
        eval_expr s e1 ValException ->
        eval_expr s (Ebinop ast_id op e1 e2) ValException
    | eval_Ebinop2: forall s e1 v1 e2 ast_id op,
        eval_expr s e1 (ValNormal v1) ->
        eval_expr s e2 ValException ->
        eval_expr s (Ebinop ast_id op e1 e2) ValException
    | eval_Ebinop3: forall s e1 v1 e2 v2 ast_id op,
        eval_expr s e1 (ValNormal v1) ->
        eval_expr s e2 (ValNormal v2) ->
        run_time_check eval_expr s (Ebinop ast_id op e1 e2) false ->
        eval_expr s (Ebinop ast_id op e1 e2) ValException
    | eval_Ebinop4: forall s e1 v1 e2 v2 ast_id op v,
        eval_expr s e1 (ValNormal v1) ->
        eval_expr s e2 (ValNormal v2) ->
        run_time_check eval_expr s (Ebinop ast_id op e1 e2) true ->
        eval_binop op (ValNormal v1) (ValNormal v2) = v ->
        v <> ValAbnormal ->
        eval_expr s (Ebinop ast_id op e1 e2) v
    | eval_Eunop1: forall s e ast_id op,
        eval_expr s e ValException ->
        eval_expr s (Eunop ast_id op e) ValException
    | eval_Eunop2: forall s e v ast_id op v1,
        eval_expr s e (ValNormal v) ->
        eval_unop op (ValNormal v) = v1 ->
        v1 <> ValAbnormal ->
        eval_expr s (Eunop ast_id op e) v1.


(** ** Command semantics *)
Inductive eval_stmt: stack -> stmt -> state -> Prop := 
    | eval_Sassign1: forall s e ast_id x,
        eval_expr s e ValException ->
        eval_stmt s (Sassign ast_id x e) SException
    | eval_Sassign2: forall s e v x s1 ast_id,
        eval_expr s e (ValNormal v) ->
        update s x (Value v) = Some s1 -> (* needs the type check on both sides *)
        eval_stmt s (Sassign ast_id x e) (SNormal s1)
    | eval_Sseq1: forall s c1 ast_id c2,
        eval_stmt s c1 SException ->
        eval_stmt s (Sseq ast_id c1 c2) SException
    | eval_Sseq2: forall ast_id s s1 s2 c1 c2,
        eval_stmt s c1 (SNormal s1) ->
        eval_stmt s1 c2 s2 ->
        eval_stmt s (Sseq ast_id c1 c2) s2
    | eval_Sifthen: forall s b ast_id c,
        eval_expr s b ValException ->
        eval_stmt s (Sifthen ast_id b c) SException
    | eval_Sifthen_True: forall s b c s1 ast_id,
        eval_expr s b (ValNormal (Bool true)) ->
        eval_stmt s c s1 ->
        eval_stmt s (Sifthen ast_id b c) s1
    | eval_Sifthen_False: forall s b ast_id c,
        eval_expr s b (ValNormal (Bool false)) ->
        eval_stmt s (Sifthen ast_id b c) (SNormal s)
    | eval_Swhile: forall s b ast_id c,
        eval_expr s b ValException ->
        eval_stmt s (Swhile ast_id b c) SException
    | eval_Swhile_True1: forall s b c ast_id,
        eval_expr s b (ValNormal (Bool true)) ->
        eval_stmt s c SException ->
        eval_stmt s (Swhile ast_id b c) SException
    | eval_Swhile_True2: forall s b c s1 ast_id s2,
        eval_expr s b (ValNormal (Bool true)) ->
        eval_stmt s c (SNormal s1) ->
        eval_stmt s1 (Swhile ast_id b c) s2 ->
        eval_stmt s (Swhile ast_id b c) s2
    | eval_Swhile_False: forall s b ast_id c,
        eval_expr s b (ValNormal (Bool false)) ->
        eval_stmt s (Swhile ast_id b c) (SNormal s).

(* - - - - - - - - - - - - - - - - - - - - - - - - - - - -  - - - - - - *)

(** * Functional Semantics *)
(** ** Expression semantics *)
(* here use 'Function' instead of 'Fixpoint' in order to use tactic 'functional induction (f_eval_expr _ _)' in proofs *)
Function f_eval_expr (s: stack) (e: expr): return_val :=
    match e with
    | Econst _ v => eval_constant v
    | Evar _ x =>
        match (fetch x s) with  (* here we have not considered the variable's mode *)
        | Some v => ValNormal v
        | None => ValAbnormal
        end
    | Ebinop _ op e1 e2 =>
        match f_eval_expr s e1 with
        | ValNormal v1 => 
            match f_eval_expr s e2 with
            | ValNormal v2 => eval_binop op (ValNormal v1) (ValNormal v2)
            | ValException => ValException
            | ValAbnormal => ValAbnormal
            end
        | ValException => ValException
        | ValAbnormal => ValAbnormal
        end   
    | Eunop _ op e => 
        match f_eval_expr s e with
        | ValNormal v => eval_unop op (ValNormal v)
        | ValException => ValException
        | ValAbnormal => ValAbnormal
        end
    end.

(** ** Command semantics *)
Function f_eval_stmt k (s: stack) (c: stmt) {struct k}: state := 
  match k with
  | 0 => SUnterminated
  | S k' => 
    match c with
    | Sassign ast_id x e =>
        match f_eval_expr s e with (* exceptions maybe raised either in evaluation of e or when looking up x  *)
        | ValNormal v => 
            match update s x (Value v) with
            | Some s1 => SNormal s1
            | None => SAbnormal
            end
        | ValException => SException
        | ValAbnormal => SAbnormal
        end
    | Sseq ast_id c1 c2 =>
        match f_eval_stmt k' s c1 with
        | SNormal s1 => f_eval_stmt k' s1 c2
        | SException => SException
        | SUnterminated => SUnterminated
        | SAbnormal => SAbnormal
        end
    | Sifthen ast_id b c =>
        match f_eval_expr s b with
        | ValNormal (Bool true) => f_eval_stmt k' s c
        | ValNormal (Bool false) => SNormal s
        | ValException => SException
        | _ => SAbnormal
        end
    | Swhile ast_id b c => 
        match f_eval_expr s b with
        | ValNormal (Bool true) => 
            match f_eval_stmt k' s c with
            | SNormal s1 => f_eval_stmt k' s1 (Swhile ast_id b c)
            | SException => SException
            | SUnterminated => SUnterminated
            | SAbnormal => SAbnormal
            end
        | ValNormal (Bool false) => SNormal s
        | ValException => SException
        | _ => SAbnormal
        end
    end
  end.

(* - - - - - - - - - - - - - - - - - - - - - - - - - - - -  - - - - - - *)
(** basic lemmas *)
Lemma expr_type_infer: forall op v1 v2 n,
    eval_binop op v1 v2 = ValNormal (Int n) -> 
        (exists n1 n2, v1 = ValNormal (Int n1) /\ v2 = ValNormal (Int n2)).
Proof.
    intros.
    unfold eval_binop in H. 
    destruct v1 as [v1' | | ]; 
    destruct v2 as [v2' | | ];
    destruct op; 
    simpl in H; try inversion H;
    destruct v1'; 
    destruct v2'; 
    simpl in H; try inversion H;
    try (exists n0, n1; auto).
Qed.

Lemma expr_type_infer': forall op v1 v2 n,
    eval_binop op v1 v2 = ValNormal (Bool n)  -> 
        (exists n1 n2, v1 = ValNormal (Int n1) /\ v2 = ValNormal (Int n2)) \/ 
        (exists n1 n2, v1 = ValNormal (Bool n1) /\ v2 = ValNormal (Bool n2)).
Proof.
    intros.
    unfold eval_binop in H.
    destruct v1 as [v1' | | ]; 
    destruct v2 as [v2' | | ]; 
    destruct op; 
    simpl in H; try inversion H;
    destruct v1'; 
    destruct v2';
    simpl in H; try inversion H.
    left; exists n0, n1; auto.
    left; exists n0, n1; auto.
    right; exists b, b0; auto.
    right; exists b, b0; auto.
    left; exists n0, n1; auto.
Qed.

(* - - - - - - - - - - - - - - - - - - - - - - - - - - - -  - - - - - - *)

(** * Bisimulation Between Relational And Functional Semantics *)

Lemma eval_expr_unique: forall s e v1 v2,
    eval_expr s e (ValNormal v1) ->
    eval_expr s e (ValNormal v2) ->
    v1 = v2.
Proof.
    induction e; 
    intros v1 v2 h1 h2;
    inversion h1; subst; 
    inversion h2; subst.
  - rewrite H3 in H4; inversion H4; subst.
    auto.
  - rewrite H1 in H2; inversion H2; auto.
  - specialize (IHe1 _ _ H3 H4).
    specialize (IHe2 _ _ H5 H10).
    subst.
    rewrite H13 in H8.
    inversion H8; auto.
  - specialize (IHe _ _ H1 H2).
    subst.
    destruct op, op0.
    rewrite H6 in H3.
    inversion H3; auto.
Qed.

Lemma eval_stmt_state : forall s p s',
        eval_stmt s p s' ->                        (* s' is either a normal state or an exception *)
            (exists v, s' = SNormal v) \/ s' = SException.
Proof.
    intros s p s' h.
    induction h;
    try match goal with
    | [ |- (exists v, SNormal ?v1 = SNormal v) \/ _ ] => left; exists v1; reflexivity
    | [ |- context [ _ \/ ?A = ?A ] ] => right; reflexivity
    end; auto.
Qed.

Lemma Zeq_zero_true: forall v,
    Zeq_bool v 0 = true <-> 
    is_not_zero v false.
Proof.
    intros v.
    split; intros h.
  - apply Zeq_bool_eq in h.
    constructor.
    assumption.
  - inversion h; subst.
    auto.
Qed.
    
Lemma Zeq_zero_false: forall v,
    Zeq_bool v 0 = false <-> 
    is_not_zero v true.
Proof.
    intros v.
    split; intros h.
  - apply Zeq_bool_neq in h.
    constructor.
    assumption.
  - inversion h; subst.
    destruct v; intuition.
Qed.


(** ** Semantics equivalence for expression *)
Lemma f_eval_expr_correct1 : forall s e v,
                        f_eval_expr s e = ValNormal v ->
                            eval_expr s e (ValNormal v).
Proof.
    intros s e.
    functional induction (f_eval_expr s e);
    intros v0 h1;
    try inversion h1; subst.
  - constructor.
    reflexivity.
  - constructor.
    assumption.
  - specialize (IHr _ e3).
    specialize (IHr0 _ e4).
    clear H0.
    econstructor; auto; try assumption.
    + (* check division by zero *)
       destruct op;
       match goal with
       | [ |- run_time_check _ _ (Ebinop _ Odiv _ _) true ] => econstructor; [constructor | ]
       | [ |- run_time_check _ _ (Ebinop _ _ _ _) true ] => econstructor; constructor; intuition; try inversion H
       end.
       destruct v1; destruct v2; simpl in h1; try inversion h1.
       econstructor; intuition.
       apply IHr.
       apply IHr0.
       remember (Zeq_bool n0 0) as eq.
       destruct eq; try inversion h1.
       symmetry in Heqeq.
       apply Zeq_zero_false; assumption.
    + rewrite h1. 
       intuition. inversion H.
  - specialize (IHr _ e2).
    econstructor; intuition; try assumption.
    rewrite h1 in H; inversion H.
Qed.


Lemma f_eval_expr_correct2 : forall s e,
                        f_eval_expr s e = ValException ->
                            eval_expr s e ValException.
Proof.
    intros s e.
    functional induction (f_eval_expr s e);
    intros h; try inversion h.
  - destruct v; inversion h.
  - rewrite h.
    specialize (f_eval_expr_correct1 _ _ _ e3); intros hz1.
    specialize (f_eval_expr_correct1 _ _ _ e4); intros hz2.
    econstructor 5.
    apply hz1. apply hz2.
    destruct op;
    destruct v1; destruct v2;
    try inversion h.
    econstructor. 
    constructor.
    econstructor. 
    intuition.
    apply hz1.
    apply hz2.
    remember (Zeq_bool n0 0) as eq.
    symmetry in Heqeq.
    destruct eq; try inversion h1.
    apply Zeq_zero_true; assumption.
    inversion H1.  
  - specialize (IHr0 e4).
    specialize (f_eval_expr_correct1 _ _ _ e3); intros hz1.
    econstructor 4; auto.
    apply hz1.
  - specialize (IHr e3).
    constructor; assumption.
  - econstructor 8; intuition.
    apply f_eval_expr_correct1; assumption.
    repeat (progress constructor).
    rewrite h in H. 
    discriminate H.    
  - specialize (IHr e2).
    constructor; assumption.
Qed.

(** *** f_eval_expr_correct *)
Lemma f_eval_expr_correct : forall s e v,
                        (f_eval_expr s e = ValNormal v ->
                            eval_expr s e (ValNormal v)) /\
                        (f_eval_expr s e = ValException ->
                            eval_expr s e ValException).
Proof.
    split.
  - apply f_eval_expr_correct1.
  - apply f_eval_expr_correct2.
Qed.

Lemma dividor_is_zero: forall s e2 v2 ast_id e1, 
    eval_expr s e2 (ValNormal v2) ->
    run_time_check eval_expr s (Ebinop ast_id Odiv e1 e2) false ->
    v2 = Int 0.
Proof.
    intros.
    inversion H0; subst.
    inversion H1; subst.
    inversion H2; subst.
    specialize (eval_expr_unique _ _ _ _ H H9); intros hz1.
    apply Zeq_zero_true in H10. 
    apply Zeq_bool_eq in H10.
    subst.
    reflexivity.
    intuition.
Qed.

(*
Lemma dividor_is_zero: forall s e2 v2 ast_id e1, 
    eval_expr s e2 (ValNormal (Int v2)) ->
    run_time_check eval_expr s (Ebinop ast_id Odiv e1 e2) false ->
    is_not_zero v2 false.
Proof.
    intros.
    inversion H0; subst.
    inversion H1; subst.
    inversion H2; subst.
    specialize (eval_expr_unique _ _ _ _ H H8); intros hz1.
    rm_eq.
Qed.
*)

(** *** f_eval_expr_complete *)
Lemma f_eval_expr_complete : forall e s v,  
                        eval_expr e s v -> 
                            (f_eval_expr e s) = v.
Proof.
    intros e s v h.
    induction h; simpl; intros;
    repeat match goal with
    | h: fetch _ _ = _  |- _ => progress rewrite h
    | h: f_eval_expr _ _ = _ |- _ => progress rewrite h
    end;auto.
  - destruct v1; destruct v2;
    destruct op;
    inversion H; inversion H0; subst; inversion H1; 
    subst; simpl; auto;
    match goal with
    | [h1: eval_expr ?s e1 (ValNormal ?v1), h2: eval_expr ?s e1 (ValNormal ?v1') |- _ ] =>
            specialize (eval_expr_unique _ _ _ _  h1 h2); let hz := fresh "hz" in intros hz; inversion hz; subst
    end;
    match goal with
    | [h1: eval_expr ?s e2 (ValNormal ?v2), h2: eval_expr ?s e2 (ValNormal ?v2') |- _ ] =>
            specialize (eval_expr_unique _ _ _ _  h1 h2); let hz := fresh "hz" in intros hz; inversion hz; subst
    end;
    match goal with
    | [h1: eval_expr _ ?e2 (ValNormal ?v2), h2: run_time_check _ _ (Ebinop _ Odiv _ ?e2) false |- _ ] =>
            specialize (dividor_is_zero _ _ _ _ _ h1 h2); let hz := fresh "hz" in intros hz; inversion hz; subst; simpl; auto
    end.
Qed.


Ltac blam :=
  match goal with
    | H:SUnterminated = SNormal _ |- _ => inversion H
    | H:SUnterminated = SException |- _ => inversion H
    | H:SUnterminated = SAbnormal |- _ => inversion H
    | H:SAbnormal = SNormal _ |- _ => inversion H
    | H:SAbnormal = SException |- _ => inversion H
    | H:SAbnormal = SUnterminated |- _ => inversion H
    | H:SException = SNormal _ |- _ => inversion H
    | H:SException = SAbnormal |- _ => inversion H
    | H:SException = SUnterminated |- _ => inversion H
    | H:SNormal _ = SUnterminated |- _ => inversion H
    | H:SNormal _ = SException |- _ => inversion H
    | H:SNormal _ = SAbnormal |- _ => inversion H
    | H:SNormal _ = SNormal _ |- _ => inversion H;clear H;subst 
    | h:update _ _ (Value _) = _ |- _ => rewrite h
    | H : f_eval_stmt _ _ _ = _ |- _ => rewrite H
    | H : f_eval_expr _ _ = _ |- _ => rewrite H
  end;subst;simpl;auto.

Ltac invle := match goal with
    | H: (S _ <= _)%nat |- _ => (inversion H; clear H; subst;simpl)
  end.

Lemma f_eval_stmt_fixpoint: forall k s p s', 
        f_eval_stmt k s p = SNormal s' ->
        forall k':nat, (k <= k')%nat -> 
            f_eval_stmt k' s p = SNormal s'.
Proof.
    intros k s p.
    functional induction (f_eval_stmt k s p); simpl; intros; subst; simpl; auto;
    repeat progress blam.
  - invle.
    + repeat blam.
    + blam. blam.
  - invle.
    + repeat blam.
    + rewrite (IHs0 _ e1);auto with arith.
  - invle; repeat blam. rewrite (IHs0 _ H);auto with arith.
  - invle; repeat blam.
  - invle; repeat blam. rewrite (IHs0 _ e2); auto with arith.
  - invle; repeat blam.
Qed.

Lemma f_eval_stmt_fixpoint_E: forall k s p, 
        f_eval_stmt k s p = SException ->
        forall k':nat, (k <= k')%nat -> 
            f_eval_stmt k' s p = SException.
Proof.
    intros k s p.
    functional induction (f_eval_stmt k s p); simpl; intros; subst; simpl; auto;
    repeat progress blam. 
  - invle;
    blam.
  - invle;
    repeat blam.
    rewrite (f_eval_stmt_fixpoint _ _ _ _ e1); auto with arith.
  - invle;
    repeat blam.
    specialize (IHs0 e1). 
    rewrite IHs0; auto with arith. 
  - invle; 
    repeat blam.
    rewrite IHs0; auto with arith.
  - invle;
    repeat blam.
  - invle; 
    repeat blam. 
    rewrite (f_eval_stmt_fixpoint _ _ _ _ e2); auto with arith.
  - invle; 
    repeat blam.
    rewrite (IHs0 e2); auto with arith.    
  - invle; 
    repeat blam.   
Qed.


Ltac destrIH :=
  repeat progress (match goal with
                     | h: ex _ |- _  =>
                       let k := fresh "k" in
                       let hk1 := fresh "hk" in
                       destruct (h) as [k hk1];try assumption
                   end).

Ltac kgreater :=
  repeat match goal with
           | h:f_eval_stmt ?k ?s ?p = SNormal ?s' |- context [f_eval_stmt (?k + _) ?s ?p] =>
             rewrite (@f_eval_stmt_fixpoint _ _ _ _ h);auto with arith
           | h:f_eval_stmt ?k ?s ?p = SNormal ?s' |- context [f_eval_stmt (_ + ?k) ?s ?p] =>
             rewrite (@f_eval_stmt_fixpoint _ _ _ _ h);auto with arith
           | h:f_eval_stmt ?k ?s ?p = SException |- context [f_eval_stmt (?k + _) ?s ?p] =>
             rewrite (@f_eval_stmt_fixpoint_E _ _ _ h);auto with arith
           | h:f_eval_stmt ?k ?s ?p = SException |- context [f_eval_stmt (_ + ?k) ?s ?p] =>
             rewrite (@f_eval_stmt_fixpoint_E _ _ _ h);auto with arith
         end.

(** ** Semantics equivalence for command *)

Ltac rm_f_eval_expr :=
    match goal with 
    | [ h: f_eval_expr ?s ?b = ValException |- _ ] => specialize (f_eval_expr_correct2 _ _ h); intros hz1
    | [ h: f_eval_expr ?s ?b = ValNormal ?v |- _ ] => specialize (f_eval_expr_correct1 _ _ _ h); intros hz1   
(*
    | [ h: f_eval_stmt ?k ?s ?c = SException |- _ ] => specialize (f_eval_stmt_correct1 _ _ _ _ h); intros hz1
    | [ h: f_eval_stmt ?k ?s ?c = SNormal ?s1 |- _ ] => specialize (f_eval_stmt_correct1 _ _ _ _ h); intros hz1
*)
    end; auto.

Lemma f_eval_stmt_correct1 : forall k s p s',
        f_eval_stmt k s p = SNormal s' ->
          eval_stmt s p (SNormal s').
Proof.
    intros k s p.
    functional induction (f_eval_stmt k s p);
    intros s' H; try inversion H; subst.
  - (* Sassign *)
    econstructor.
    rm_f_eval_expr.
    apply hz1.
    assumption.
  - (* Sseq *)
    specialize (IHs0 _ e1).
    specialize (IHs1 _ H).
    econstructor.
    apply IHs0.
    blam.
  - (* Cifthen_True *)
    specialize (IHs0 _ H).
    econstructor.
    rm_f_eval_expr. 
    blam.
  - (* Cifthen_False *)
    eapply eval_Sifthen_False.
    rm_f_eval_expr.
  - (* Swhile_True *)
    specialize (IHs0 _ e2).
    specialize (IHs1 _ H).
    econstructor.
    rm_f_eval_expr.
    apply IHs0. 
    blam.
  - (* Swhile_False *)
    eapply eval_Swhile_False.
    rm_f_eval_expr.
Qed.

Ltac rm_f_eval_stmt :=
    match goal with 
    | [ h: f_eval_stmt ?k ?s ?c = SNormal ?s1 |- _ ] => specialize (f_eval_stmt_correct1 _ _ _ _ h); intros hz1
    end; auto.

Lemma f_eval_stmt_correct2 : forall k s p,
        f_eval_stmt k s p = SException ->
          eval_stmt s p SException.
Proof.
    intros k s p.
    functional induction (f_eval_stmt k s p);
    intros H; try inversion H; subst.
  - (* Sassign *)
    econstructor.
    rm_f_eval_expr.
  - (* Sseq *)
    specialize (IHs1 H).
    econstructor.
    rm_f_eval_stmt.
    apply hz1.
    blam.
  - specialize (IHs0 e1).
    econstructor.
    assumption.    
  - (* Cifthen *)
    specialize (IHs0 H).
    econstructor.
    rm_f_eval_expr.
    blam.
  - econstructor.
    specialize (f_eval_expr_correct2 _ _ e1); intros hz1. 
    assumption.
  - (* Swhile *)
    specialize (IHs1 H).
    econstructor.
    rm_f_eval_expr.
    rm_f_eval_stmt.
    apply hz1.
    blam.
  - constructor 9.
    rm_f_eval_expr.
    specialize (IHs0 e2); assumption.    
  - econstructor.
    rm_f_eval_expr.
Qed.

Ltac rm_f_eval :=
    match goal with 
    | [ h: f_eval_expr ?s ?b = ValException |- _ ] => specialize (f_eval_expr_correct2 _ _ h); intros hz1
    | [ h: f_eval_expr ?s ?b = ValNormal ?v |- _ ] => specialize (f_eval_expr_correct1 _ _ _ h); intros hz1   
    | [ h: f_eval_stmt ?k ?s ?c = SException |- _ ] => specialize (f_eval_stmt_correct2 _ _ _ h); intros hz1
    | [ h: f_eval_stmt ?k ?s ?c = SNormal ?s1 |- _ ] => specialize (f_eval_stmt_correct1 _ _ _ _ h); intros hz1
    end; auto.

(** *** f_eval_stmt_correct *)
Lemma f_eval_stmt_correct : forall k s p s',
        (f_eval_stmt k s p = SNormal s' ->
          eval_stmt s p (SNormal s')) /\ 
        (f_eval_stmt k s p = SException ->
          eval_stmt s p SException).
Proof.
    intros.
    split; intros;
    rm_f_eval.
Qed.

(** *** f_eval_stmt_complete *)
Lemma f_eval_stmt_complete : forall s p s',
        eval_stmt s p s' ->                        (* s' is either a normal state or an exception *)
            exists k, f_eval_stmt k s p = s'.
Proof. 
  intros s p s' H;
  induction H;
  try match goal with
  [ h: eval_expr ?s ?e ValException |- exists k, _ = SException] => 
          exists 1%nat; simpl;
          rewrite (f_eval_expr_complete _ _ _ h);
          reflexivity
  end.
  (* 1. Sassign *)
  - exists 1%nat. simpl.
    rewrite (f_eval_expr_complete _ _ _ H).
    blam.   
  (* 2. Sseq *)
  - destrIH.
    exists (S k); simpl.
    blam.
  - destrIH.
    exists (S (k0+k)); simpl.
    kgreater.
    specialize (eval_stmt_state _ _ _ H0); intros hz1.
    destruct hz1 as [hz2 | hz2]; try rm_exists; subst;
    kgreater.
  (* 3. Sifthen *)
  - destrIH.
    exists (S k); simpl.
    rewrite (f_eval_expr_complete _ _ _ H).
    assumption.
  - exists 1%nat. simpl.
    rewrite (f_eval_expr_complete _ _ _ H).
    reflexivity.
  (* 4. Swhile *)
  - destrIH.
    exists (S k); simpl.
    rewrite (f_eval_expr_complete _ _ _ H).
    blam.
  - destrIH.
    exists (S (k0+k)); simpl.
    rewrite (f_eval_expr_complete _ _ _ H).    
    kgreater.
    specialize (eval_stmt_state _ _ _ H1); intros hz1.
    destruct hz1 as [hz2 | hz2]; try rm_exists; subst;
    kgreater.
  - exists 1%nat. simpl.
    rewrite (f_eval_expr_complete _ _ _ H).
    reflexivity.
Qed.







