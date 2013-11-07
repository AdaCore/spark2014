(** 
_AUTHOR_

<<
Zhi Zhang
Departmnt of Computer and Information Sciences
Kansas State University
zhangzhi@ksu.edu
>>
*)

Require Export values.
Require Export environment.
Require Export util.
Require Export checks.

(** * Relational Semantics (big-step) *)
(** interpret the literal expressions *)
Definition eval_literal (l: literal): value :=
    match l with
    | Integer_Literal v => (Int v)
    | Boolean_Literal b => (Bool b)
    end.

(** interpret the binary operators *)
Inductive eval_bin_expr: binary_operator -> value -> value -> value -> Prop :=
    | Bin_Eq: forall v1 v2 b,
        Zeq_bool v1 v2 = b ->
        eval_bin_expr Equal (Int v1) (Int v2) (Bool b)
    | Bin_Ne: forall v1 v2 b,
        Zneq_bool v1 v2 = b ->
         eval_bin_expr Not_Equal (Int v1) (Int v2) (Bool b)
    | Bin_Gt: forall v1 v2 b,
        Zgt_bool v1 v2 = b ->
        eval_bin_expr Greater_Than (Int v1) (Int v2) (Bool b)
    | Bin_Ge: forall v1 v2 b,
        Zge_bool v1 v2 = b ->
        eval_bin_expr Greater_Than_Or_Equal (Int v1) (Int v2) (Bool b)
    | Bin_Lt: forall v1 v2 b,
        Zlt_bool v1 v2 = b ->
        eval_bin_expr Less_Than (Int v1) (Int v2) (Bool b)
    | Bin_Le: forall v1 v2 b,
        Zle_bool v1 v2 = b ->
        eval_bin_expr Less_Than_Or_Equal (Int v1) (Int v2) (Bool b)
    | Bin_And: forall v1 v2 b,
        andb v1 v2 = b ->
        eval_bin_expr And (Bool v1) (Bool v2) (Bool b)
    | Bin_Or: forall v1 v2 b,
        orb v1 v2 = b ->
        eval_bin_expr Or (Bool v1) (Bool v2) (Bool b)
    | Bin_Plus: forall v1 v2 v3,
        (v1 + v2)%Z =v3 ->
        eval_bin_expr Plus (Int v1) (Int v2) (Int v3)
    | Bin_Minus: forall v1 v2 v3,
        (v1 - v2)%Z =v3 ->
        eval_bin_expr Minus (Int v1) (Int v2) (Int v3)
    | Bin_Mul: forall v1 v2 v3,
        (v1 * v2)%Z =v3 ->
        eval_bin_expr Multiply (Int v1) (Int v2) (Int v3)
    | Bin_Div: forall v1 v2 v3,
        (Z.quot v1 v2)%Z =v3 ->
        eval_bin_expr Divide (Int v1) (Int v2) (Int v3).

(** interpret the unary operation *)
Inductive eval_unary_expr : unary_operator -> value -> value -> Prop :=
    | Unary_Not: forall b v,
        negb b = v ->
        eval_unary_expr Not (Bool b) (Bool v).

Lemma eval_bin_unique: forall op v1 v2 x y,
    eval_bin_expr op v1 v2 x ->
    eval_bin_expr op v1 v2 y ->
    x = y.
Proof.
    intros.
    destruct op;
    inversion H; subst; inversion H0; subst;
    auto.
Qed.

Lemma eval_unary_unique: forall uop v x y,
    eval_unary_expr uop v x ->
    eval_unary_expr uop v y ->
    x = y.
Proof.
    intros.
    destruct uop;
    inversion H; subst; inversion H0; subst;
    auto.
Qed.


(** ** Expression semantics *)
(**
    for binary expression and unary expression, if a run time error 
    is detected in any of its child expressions, then return a run
    time error; for binary expression (e1 op e2), if both e1 and e2 
    are evaluated to some normal value, then run time checks are
    performed according to the checking rules specified for the 
    operator 'op', whenever the check fails (returning false), a run 
    time error is detected and the program is terminated, otherwise, 
    normal binary operation result is returned;
*)

Inductive eval_expr: store -> expression -> return_val -> Prop :=
    | eval_E_Literal: forall l v s ast_num,
        eval_literal l = v ->
        eval_expr s (E_Literal ast_num l) (Val_Normal v)
    | eval_E_Identifier: forall x s v ast_num,
        fetch x s = Some v ->
        eval_expr s (E_Identifier ast_num x) (Val_Normal v)
    | eval_E_Binary_Operation1: forall s e1 ast_num op e2,
        eval_expr s e1 Val_Run_Time_Error ->
        eval_expr s (E_Binary_Operation ast_num op e1 e2) Val_Run_Time_Error
    | eval_E_Binary_Operation2: forall s e1 v1 e2 ast_num op,
        eval_expr s e1 (Val_Normal v1) ->
        eval_expr s e2 Val_Run_Time_Error ->
        eval_expr s (E_Binary_Operation ast_num op e1 e2) Val_Run_Time_Error
    | eval_E_Binary_Operation3: forall s e1 v1 e2 v2 ast_num op,
        eval_expr s e1 (Val_Normal v1) ->
        eval_expr s e2 (Val_Normal v2) ->
        do_check op v1 v2 false ->
        eval_expr s (E_Binary_Operation ast_num op e1 e2) Val_Run_Time_Error
    | eval_E_Binary_Operation4: forall s e1 v1 e2 v2 ast_num op v,
        eval_expr s e1 (Val_Normal v1) ->
        eval_expr s e2 (Val_Normal v2) ->
        do_check op v1 v2 true ->
        eval_bin_expr op v1 v2 v ->
        eval_expr s (E_Binary_Operation ast_num op e1 e2) (Val_Normal v)
    | eval_E_Unary_Operation1: forall s e ast_num op,
        eval_expr s e Val_Run_Time_Error ->
        eval_expr s (E_Unary_Operation ast_num op e) Val_Run_Time_Error
    | eval_E_Unary_Operation2: forall s e v ast_num op v1,
        eval_expr s e (Val_Normal v) ->
        eval_unary_expr op v v1 ->
        eval_expr s (E_Unary_Operation ast_num op e) (Val_Normal v1).


(** ** Statement semantics *)
(** 
   in a statement evaluation, whenever a run time error is detected 
   in the evaluation of its sub-statements or sub-component, the 
   evaluation is terminated and return a run time error; otherwise, 
   evaluate the statement into a normal state; 
*)

Inductive eval_stmt: store -> statement -> state -> Prop := 
    | eval_S_Assignment1: forall s e ast_num x,
        eval_expr s e Val_Run_Time_Error ->
        eval_stmt s (S_Assignment ast_num x e) S_Run_Time_Error
    | eval_S_Assignment2: forall s e v x s1 ast_num,
        eval_expr s e (Val_Normal v) ->
        update s x (Value v) = Some s1 ->
        eval_stmt s (S_Assignment ast_num x e) (S_Normal s1)
    | eval_S_Sequence1: forall s c1 ast_num c2,
        eval_stmt s c1 S_Run_Time_Error ->
        eval_stmt s (S_Sequence ast_num c1 c2) S_Run_Time_Error
    | eval_S_Sequence2: forall ast_num s s1 s2 c1 c2,
        eval_stmt s c1 (S_Normal s1) ->
        eval_stmt s1 c2 s2 ->
        eval_stmt s (S_Sequence ast_num c1 c2) s2
    | eval_S_If: forall s b ast_num c,
        eval_expr s b Val_Run_Time_Error ->
        eval_stmt s (S_If ast_num b c) S_Run_Time_Error
    | eval_S_If_True: forall s b c s1 ast_num,
        eval_expr s b (Val_Normal (Bool true)) ->
        eval_stmt s c s1 ->
        eval_stmt s (S_If ast_num b c) s1
    | eval_S_If_False: forall s b ast_num c,
        eval_expr s b (Val_Normal (Bool false)) ->
        eval_stmt s (S_If ast_num b c) (S_Normal s)
    | eval_S_While_Loop: forall s b ast_num c,
        eval_expr s b Val_Run_Time_Error ->
        eval_stmt s (S_While_Loop ast_num b c) S_Run_Time_Error
    | eval_S_While_Loop_True1: forall s b c ast_num,
        eval_expr s b (Val_Normal (Bool true)) ->
        eval_stmt s c S_Run_Time_Error ->
        eval_stmt s (S_While_Loop ast_num b c) S_Run_Time_Error
    | eval_S_While_Loop_True2: forall s b c s1 ast_num s2,
        eval_expr s b (Val_Normal (Bool true)) ->
        eval_stmt s c (S_Normal s1) ->
        eval_stmt s1 (S_While_Loop ast_num b c) s2 ->
        eval_stmt s (S_While_Loop ast_num b c) s2
    | eval_S_While_Loop_False: forall s b ast_num c,
        eval_expr s b (Val_Normal (Bool false)) ->
        eval_stmt s (S_While_Loop ast_num b c) (S_Normal s).



(** * Functional Semantics *)

(** for relational semantics of expression and statement, we also 
    provide its corresponding version of functional semantics, and 
    prove that they are semantics equivalent;
    relational semantics encode the formal semantics rules, while
    functional semantics is useful to familiarize oneself with the 
    SPARK 2014 semantics, and validate it experimentally by testing, 
    and it also helps to fix the program if the program exhibits 
    undefined behavior;
    
    Bisimulation between relational and functional semantics are
    proved for the following pairs of evaluations: 
    
    - f_eval_binexpr <-> eval_binexpr;
    
    - f_eval_unaryexpr <-> eval_unaryexpr;
    
    - f_eval_expr <-> eval_expr;

    - f_eval_stmt <-> eval_stmt;
*)

(** interpret the binary operation for each binary operator *)
Definition f_eval_bin_expr (op: binary_operator) (v1: value) (v2: value): return_val :=
    match op with
    | Equal => Val.eq v1 v2
    | Not_Equal => Val.ne v1 v2
    | Greater_Than => Val.gt v1 v2
    | Greater_Than_Or_Equal => Val.ge v1 v2
    | Less_Than => Val.lt v1 v2
    | Less_Than_Or_Equal => Val.le v1 v2
    | And => Val.and v1 v2
    | Or => Val.or v1 v2
    | Plus => Val.add v1 v2
    | Minus => Val.sub v1 v2
    | Multiply => Val.mul v1 v2
    | Divide => Val.div v1 v2
    end.

(** interpret the unary operation *)
Definition f_eval_unary_expr (op: unary_operator) (v: value): return_val :=
    match op with
    | Not => Val.not v
    end.

(** ** Expression semantics *)

(**
    in functional semantics for expression, it returns either a 
    normal value or a run time error or go abnormal, the run time 
    checks (for example, division by zero check) are encoded inside 
    the semantics;
*)
(* here use 'Function' instead of 'Fixpoint' in order to use 
   tactic 'functional induction (f_eval_expr _ _)' in proofs;
*)
Function f_eval_expr (s: store) (e: expression): return_val :=
    match e with
    | E_Literal _ v => Val_Normal (eval_literal v)
    | E_Identifier _ x =>
        match (fetch x s) with
        | Some v => Val_Normal v
        | None => Val_Abnormal
        end
    | E_Binary_Operation _ op e1 e2 =>
        match f_eval_expr s e1 with
        | Val_Normal v1 => 
            match f_eval_expr s e2 with
            | Val_Normal v2 => 
                match f_do_check op v1 v2 with
                | Some true => f_eval_bin_expr op v1 v2
                | Some false => Val_Run_Time_Error
                | _ => Val_Abnormal
                end
            | Val_Run_Time_Error => Val_Run_Time_Error
            | Val_Abnormal => Val_Abnormal
            end
        | Val_Run_Time_Error => Val_Run_Time_Error
        | Val_Abnormal => Val_Abnormal
        end   
    | E_Unary_Operation _ op e => 
        match f_eval_expr s e with
        | Val_Normal v => f_eval_unary_expr op v
        | Val_Run_Time_Error => Val_Run_Time_Error
        | Val_Abnormal => Val_Abnormal
        end
    end.

(** ** Statement semantics *)
(** 
   in the functional semantics for statement, 'k' denotes the execution 
   steps, whenever it reaches 0, an untermination state is returned;
   otherwise, it returns either a normal state, or a run time error 
   or an abnormal state; run time checks (for example, division by 
   zero check) are encoded inside the functional semantics;
*)

Function f_eval_stmt k (s: store) (c: statement) {struct k}: state := 
  match k with
  | 0 => S_Unterminated
  | S k' => 
    match c with
    | S_Assignment ast_num x e =>
        match f_eval_expr s e with
        | Val_Normal v => 
            match update s x (Value v) with
            | Some s1 => S_Normal s1
            | None => S_Abnormal
            end
        | Val_Run_Time_Error => S_Run_Time_Error
        | Val_Abnormal => S_Abnormal
        end
    | S_Sequence ast_num c1 c2 =>
        match f_eval_stmt k' s c1 with
        | S_Normal s1 => f_eval_stmt k' s1 c2
        | S_Run_Time_Error => S_Run_Time_Error
        | S_Unterminated => S_Unterminated
        | S_Abnormal => S_Abnormal
        end
    | S_If ast_num b c =>
        match f_eval_expr s b with
        | Val_Normal (Bool true) => f_eval_stmt k' s c
        | Val_Normal (Bool false) => S_Normal s
        | Val_Run_Time_Error => S_Run_Time_Error
        | _ => S_Abnormal
        end
    | S_While_Loop ast_num b c => 
        match f_eval_expr s b with
        | Val_Normal (Bool true) => 
            match f_eval_stmt k' s c with
            | S_Normal s1 => f_eval_stmt k' s1 (S_While_Loop ast_num b c)
            | S_Run_Time_Error => S_Run_Time_Error
            | S_Unterminated => S_Unterminated
            | S_Abnormal => S_Abnormal
            end
        | Val_Normal (Bool false) => S_Normal s
        | Val_Run_Time_Error => S_Run_Time_Error
        | _ => S_Abnormal
        end
    end
  end.



(** basic lemmas *)

(** for any expression e, if it can be evaluated to v1 and v2 in the
    same state s, then v1 and v2 should be the same; 
*)
Lemma eval_expr_unique: forall s e v1 v2,
    eval_expr s e (Val_Normal v1) ->
    eval_expr s e (Val_Normal v2) ->
    v1 = v2.
Proof.
    induction e; 
    intros v1 v2 h1 h2;
    inversion h1; subst;
    inversion h2; subst;
    auto.
  - rewrite H1 in H2; 
    inversion H2; auto.
  - specialize (IHe1 _ _ H5 H9).
    specialize (IHe2 _ _ H6 H10).
    subst.
    specialize (eval_bin_unique _ _ _ _ _ H8 H12); intros hz1; subst.
    auto.
  - specialize (IHe _ _ H3 H5). subst.
    destruct op, op0.
    specialize (eval_unary_unique _ _ _ _ H4 H6); intros hz1; subst.
    auto.
Qed.

(** 
    for any expression e evaluated under the state s, if it can be 
    evaluated to a value v with respect to the relational semantics 
    eval_expr, then the result value v should be either a normal 
    value or a run time error;
*)
Lemma eval_expr_state : forall s e v,
        eval_expr s e v -> (* v should be either a normal value or a run time error *)
            (exists v0, v = Val_Normal v0) \/ v = Val_Run_Time_Error.
Proof.
    intros s e v h.
    induction h;
    try match goal with
    | [ |- (exists v, Val_Normal ?v1 = Val_Normal v) \/ _ ] => left; exists v1; reflexivity
    | [ |- context [ _ \/ ?A = ?A ] ] => right; reflexivity
    end; auto.
Qed.

(** 
    for any statement c starting from the initial state s, if it 
    terminates in a state s' with respect to the relational semantics 
    eval_stmt, then the result state s' should be either a normal 
    state or a run time error. In relational semantics eval_stmt, 
    all statements that can go abnormal are excluded;
*)
Lemma eval_stmt_state : forall s c s',
        eval_stmt s c s' -> (* s' is either a normal state or a run time error *)
            (exists v, s' = S_Normal v) \/ s' = S_Run_Time_Error.
Proof.
    intros s c s' h.
    induction h;
    try match goal with
    | [ |- (exists v, S_Normal ?v1 = S_Normal v) \/ _ ] => left; exists v1; reflexivity
    | [ |- context [ _ \/ ?A = ?A ] ] => right; reflexivity
    end; auto.
Qed.

(** * Bisimulation Between Relational And Functional Semantics *)

(** bisimulation proof between f_eval_binexpr and eval_binexpr:
    - f_eval_bin_expr_correct
    - f_eval_bin_expr_complete
*)
Lemma f_eval_bin_expr_correct: forall op v1 v2 v,
    f_eval_bin_expr op v1 v2 = Val_Normal v ->
    eval_bin_expr op v1 v2 v.
Proof.
    intros op v1 v2 v h1.
    destruct op;
    match goal with 
    |[|- eval_bin_expr Divide _ _ _] => idtac
    |[|- eval_bin_expr ?op _ _ _] =>
        destruct v1, v2;
        simpl in h1; inversion h1; subst;
        constructor; auto
    end.
    destruct v1, v2; simpl in h1; inversion h1.
    constructor.
    remember (Zeq_bool n0 0) as x.
    reflexivity.
Qed.

Lemma f_eval_bin_expr_complete: forall op v1 v2 v,
    eval_bin_expr op v1 v2 v ->
    f_eval_bin_expr op v1 v2 = Val_Normal v.
Proof.
    intros op v1 v2 v h1.
    induction h1;
    rewrite <- H;
    simpl; auto.
Qed.

(** bisimulation proof between f_eval_unaryexpr and eval_unaryexpr: 
    - f_eval_unary_expr_correct
    - f_eval_unary_expr_complete
*)
Lemma f_eval_unary_expr_correct: forall op v v',
    f_eval_unary_expr op v = Val_Normal v' ->
    eval_unary_expr op v v'.
Proof.
    intros.
    destruct op; simpl in H.
    destruct v; inversion H; subst.
    constructor; auto.
Qed.

Lemma f_eval_unary_expr_complete: forall op v v',
    eval_unary_expr op v v' ->
    f_eval_unary_expr op v = Val_Normal v'.
Proof.
    intros op v v' h1;
    induction h1;
    rewrite <- H;
    simpl; auto.
Qed.

(** ** Bisimulation between f_eval_expr and eval_expr for expression Semantics *)
(** a help lemma to prove the theorem: f_eval_expr_correct *)
Lemma f_eval_expr_correct1 : forall s e v,
                        f_eval_expr s e = Val_Normal v ->
                            eval_expr s e (Val_Normal v).
Proof.
    intros s e.
    functional induction (f_eval_expr s e);
    intros v0 h1;
    try inversion h1; subst.
  - constructor;
    reflexivity.
  - constructor;
    assumption.
  - specialize (IHr _ e3).
    specialize (IHr0 _ e4).
    rewrite H0.
    econstructor.
    exact IHr. exact IHr0.
    + apply f_do_check_correct.
      auto.
    + apply f_eval_bin_expr_correct; 
      auto.
  - specialize (IHr _ e2).
    rewrite h1.
    econstructor. 
    exact IHr.
    destruct op. 
    simpl in h1. 
    destruct v; inversion h1; subst.
    constructor; auto.
Qed.

(** another help lemma to prove the theorem: f_eval_expr_correct *)
Lemma f_eval_expr_correct2 : forall s e,
                        f_eval_expr s e = Val_Run_Time_Error ->
                            eval_expr s e Val_Run_Time_Error.
Proof.
    intros s e.
    functional induction (f_eval_expr s e);
    intros h; try inversion h.
  - destruct op, v1, v2;
    simpl in h; inversion h.
  - specialize (f_eval_expr_correct1 _ _ _ e3); intros hz1.
    specialize (f_eval_expr_correct1 _ _ _ e4); intros hz2.
    eapply eval_E_Binary_Operation3.
    apply hz1. apply hz2.
    apply f_do_check_correct; auto.
  - specialize (f_eval_expr_correct1 _ _ _ e3); intros hz1.
    specialize (IHr0 e4).
    eapply eval_E_Binary_Operation2; auto.
    exact hz1.
  - specialize (IHr e3).
    constructor; assumption.
  - destruct op;
    destruct v; inversion h. 
  - specialize (IHr e2).
    constructor; assumption.
Qed.

(** *** f_eval_expr_correct *)
(** 
    for an expression e evaluated under the state s with respect to
    the functional semantics f_eval_expr, whenever it returns a 
    normal value v or terminates in a run time error, 
    the relation between s, e and evaluation result should also be 
    satisfied with respect to the relational semantics 'eval_expr';
*)
Theorem f_eval_expr_correct : forall s e v,
                        (f_eval_expr s e = Val_Normal v ->
                            eval_expr s e (Val_Normal v)) /\
                        (f_eval_expr s e = Val_Run_Time_Error ->
                            eval_expr s e Val_Run_Time_Error).
Proof.
    split.
  - apply f_eval_expr_correct1.
  - apply f_eval_expr_correct2.
Qed.


(** *** f_eval_expr_complete *)
(** 
   for any expression e, if it can be evaluated to a value v under
   state s with respect to the relational semantics 'eval_expr', 
   then when we evalute e under the same state s in functional
   semantics 'f_eval_expr', it should return the same result v;
*)
Theorem f_eval_expr_complete : forall e s v,  
                        eval_expr e s v -> 
                            (f_eval_expr e s) = v.
Proof.
    intros e s v h.
    induction h; simpl; intros;
    repeat match goal with
    | h: fetch _ _ = _  |- _ => progress rewrite h
    | h: f_eval_expr _ _ = _ |- _ => progress rewrite h
    end;auto.
  - rewrite H; reflexivity.
  - specialize (f_do_check_complete _ _ _ _ H); intros hz1.
    rewrite hz1.
    reflexivity.
  - destruct v1; destruct v2;
    destruct op;
    inversion H0; subst; simpl; auto.
    + (* overflow check for Plus *)
      inversion H; subst.
      rewrite H3; auto.
      unfold not in H2; intuition.
    + (* overflow check for Minus *)
      inversion H; subst.
      rewrite H3; auto.
      unfold not in H2; intuition.
    + (* overflow check for Multiply *)
      inversion H; subst.
      rewrite H3; auto.
      unfold not in H2; intuition.
    + (* both division by zero check and overflow check *)
      inversion H; subst.
      rewrite H3; auto.
      rm_false_hyp.
  - destruct op.
    inversion H; subst.
    auto.
Qed.

Ltac apply_inv :=
  match goal with
    | H:S_Unterminated = S_Normal _ |- _ => inversion H
    | H:S_Unterminated = S_Run_Time_Error |- _ => inversion H
    | H:S_Unterminated = S_Abnormal |- _ => inversion H
    | H:S_Abnormal = S_Normal _ |- _ => inversion H
    | H:S_Abnormal = S_Run_Time_Error |- _ => inversion H
    | H:S_Abnormal = S_Unterminated |- _ => inversion H
    | H:S_Run_Time_Error = S_Normal _ |- _ => inversion H
    | H:S_Run_Time_Error = S_Abnormal |- _ => inversion H
    | H:S_Run_Time_Error = S_Unterminated |- _ => inversion H
    | H:S_Normal _ = S_Unterminated |- _ => inversion H
    | H:S_Normal _ = S_Run_Time_Error |- _ => inversion H
    | H:S_Normal _ = S_Abnormal |- _ => inversion H
    | H:S_Normal _ = S_Normal _ |- _ => inversion H;clear H;subst 
    | H:update _ _ (Value _) = _ |- _ => rewrite H
    | H:f_eval_stmt _ _ _ = _ |- _ => rewrite H
    | H:f_eval_expr _ _ = _ |- _ => rewrite H
  end;subst;simpl;auto.

Ltac invle := match goal with
    | H: (S _ <= _)%nat |- _ => (inversion H; clear H; subst; simpl)
  end.

(** a help lemma to prove the theorem: 'f_eval_stmt_complete',
    it means that: for any statement c, starting from initial state s, 
    if it terminates in a normal state s' within k execution steps, 
    then for any k' greater and equal than k, it should also terminate 
    in the same state s';
*)
Lemma f_eval_stmt_fixpoint: forall k s c s', 
        f_eval_stmt k s c = S_Normal s' ->
        forall k':nat, (k <= k')%nat -> 
            f_eval_stmt k' s c = S_Normal s'.
Proof.
    intros k s c.
    functional induction (f_eval_stmt k s c); simpl; intros; subst; simpl; auto;
    repeat progress apply_inv.
  - invle; repeat apply_inv.
  - invle.
    + repeat apply_inv.
    + rewrite (IHs0 _ e1);auto with arith.
  - invle; repeat apply_inv. rewrite (IHs0 _ H);auto with arith.
  - invle; repeat apply_inv.
  - invle; repeat apply_inv. rewrite (IHs0 _ e2); auto with arith.
  - invle; repeat apply_inv.
Qed.

(** another help lemma to prove the theorem: 'f_eval_stmt_complete' *)
Lemma f_eval_stmt_fixpoint_E: forall k s p, 
        f_eval_stmt k s p = S_Run_Time_Error ->
        forall k':nat, (k <= k')%nat -> 
            f_eval_stmt k' s p = S_Run_Time_Error.
Proof.
    intros k s p.
    functional induction (f_eval_stmt k s p); simpl; intros; subst; simpl; auto;
    repeat progress apply_inv. 
  - invle;
    apply_inv.
  - invle;
    repeat apply_inv.
    rewrite (f_eval_stmt_fixpoint _ _ _ _ e1); auto with arith.
  - invle;
    repeat apply_inv.
    specialize (IHs0 e1). 
    rewrite IHs0; auto with arith. 
  - invle; 
    repeat apply_inv.
    rewrite IHs0; auto with arith.
  - invle;
    repeat apply_inv.
  - invle; 
    repeat apply_inv. 
    rewrite (f_eval_stmt_fixpoint _ _ _ _ e2); auto with arith.
  - invle; 
    repeat apply_inv.
    rewrite (IHs0 e2); auto with arith.    
  - invle; 
    repeat apply_inv.   
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
           | h:f_eval_stmt ?k ?s ?p = S_Normal ?s' |- context [f_eval_stmt (?k + _) ?s ?p] =>
             rewrite (@f_eval_stmt_fixpoint _ _ _ _ h);auto with arith
           | h:f_eval_stmt ?k ?s ?p = S_Normal ?s' |- context [f_eval_stmt (_ + ?k) ?s ?p] =>
             rewrite (@f_eval_stmt_fixpoint _ _ _ _ h);auto with arith
           | h:f_eval_stmt ?k ?s ?p = S_Run_Time_Error |- context [f_eval_stmt (?k + _) ?s ?p] =>
             rewrite (@f_eval_stmt_fixpoint_E _ _ _ h);auto with arith
           | h:f_eval_stmt ?k ?s ?p = S_Run_Time_Error |- context [f_eval_stmt (_ + ?k) ?s ?p] =>
             rewrite (@f_eval_stmt_fixpoint_E _ _ _ h);auto with arith
         end.


Ltac rm_f_eval_expr :=
    match goal with 
    | [ h: f_eval_expr ?s ?b = Val_Run_Time_Error |- _ ] => 
        specialize (f_eval_expr_correct2 _ _ h); intros hz1
    | [ h: f_eval_expr ?s ?b = Val_Normal ?v |- _ ] => 
        specialize (f_eval_expr_correct1 _ _ _ h); intros hz1   
(*
    | [ h: f_eval_stmt ?k ?s ?c = S_Run_Time_Error |- _ ] => specialize (f_eval_stmt_correct1 _ _ _ _ h); intros hz1
    | [ h: f_eval_stmt ?k ?s ?c = S_Normal ?s1 |- _ ] => specialize (f_eval_stmt_correct1 _ _ _ _ h); intros hz1
*)
    end; auto.


(** ** Bisimulation between f_eval_stmt and eval_stmt for statement semantics *)

(** a help lemma to prove the theorem: 'f_eval_stmt_complete' *)
Lemma f_eval_stmt_correct1 : forall k s p s',
        f_eval_stmt k s p = S_Normal s' ->
          eval_stmt s p (S_Normal s').
Proof.
    intros k s p.
    functional induction (f_eval_stmt k s p);
    intros s' H; try inversion H; subst.
  - (* S_Assignment *)
    econstructor.
    rm_f_eval_expr.
    apply hz1.
    assumption.
  - (* S_Sequence *)
    specialize (IHs0 _ e1).
    specialize (IHs1 _ H).
    econstructor.
    apply IHs0.
    apply_inv.
  - (* S_If_True *)
    specialize (IHs0 _ H).
    econstructor.
    rm_f_eval_expr. 
    apply_inv.
  - (* S_If_False *)
    eapply eval_S_If_False.
    rm_f_eval_expr.
  - (* S_While_Loop_True *)
    specialize (IHs0 _ e2).
    specialize (IHs1 _ H).
    econstructor.
    rm_f_eval_expr.
    apply IHs0. 
    apply_inv.
  - (* S_While_Loop_False *)
    eapply eval_S_While_Loop_False.
    rm_f_eval_expr.
Qed.

Ltac rm_f_eval_stmt :=
    match goal with 
    | [ h: f_eval_stmt ?k ?s ?c = S_Normal ?s1 |- _ ] => 
        specialize (f_eval_stmt_correct1 _ _ _ _ h); intros hz1
    end; auto.

(** a help lemma to prove the theorem: 'f_eval_stmt_complete' *)
Lemma f_eval_stmt_correct2 : forall k s p,
        f_eval_stmt k s p = S_Run_Time_Error ->
          eval_stmt s p S_Run_Time_Error.
Proof.
    intros k s p.
    functional induction (f_eval_stmt k s p);
    intros H; try inversion H; subst.
  - (* S_Assignment *)
    econstructor.
    rm_f_eval_expr.
  - (* S_Sequence*)
    specialize (IHs1 H).
    econstructor.
    rm_f_eval_stmt.
    apply hz1.
    apply_inv.
  - specialize (IHs0 e1).
    econstructor.
    assumption.    
  - (* C_If *)
    specialize (IHs0 H).
    econstructor.
    rm_f_eval_expr.
    apply_inv.
  - econstructor.
    specialize (f_eval_expr_correct2 _ _ e1); intros hz1. 
    assumption.
  - (* S_While_Loop *)
    specialize (IHs1 H).
    econstructor.
    rm_f_eval_expr.
    rm_f_eval_stmt.
    apply hz1.
    apply_inv.
  - constructor 9.
    rm_f_eval_expr.
    specialize (IHs0 e2); assumption.    
  - econstructor.
    rm_f_eval_expr.
Qed.

Ltac rm_f_eval :=
    match goal with 
    | [ h: f_eval_expr ?s ?b = Val_Run_Time_Error |- _ ] => specialize (f_eval_expr_correct2 _ _ h); intros hz1
    | [ h: f_eval_expr ?s ?b = Val_Normal ?v |- _ ] => specialize (f_eval_expr_correct1 _ _ _ h); intros hz1   
    | [ h: f_eval_stmt ?k ?s ?c = S_Run_Time_Error |- _ ] => specialize (f_eval_stmt_correct2 _ _ _ h); intros hz1
    | [ h: f_eval_stmt ?k ?s ?c = S_Normal ?s1 |- _ ] => specialize (f_eval_stmt_correct1 _ _ _ _ h); intros hz1
    end; auto.

(** *** f_eval_stmt_correct *)
(** 
   for any statement c starting from initial state s, if it returns 
   a normal state s' or terminates in a run time error within k steps
   with respect to the functional semantics 'f_eval_stmt', then the 
   relation between s, c and the resulting state should also be 
   satisfied with respect to the relational semantics 'eval_stmt';
*)
Theorem f_eval_stmt_correct : forall k s c s',
        (f_eval_stmt k s c = S_Normal s' ->
          eval_stmt s c (S_Normal s')) /\ 
        (f_eval_stmt k s c = S_Run_Time_Error ->
          eval_stmt s c S_Run_Time_Error).
Proof.
    intros.
    split; intros;
    rm_f_eval.
Qed.

(** *** f_eval_stmt_complete *)
(** 
   the reverse direction is also satisfied: for any statement c, 
   whenever it's executed starting from initial state s and return 
   a new state s' with regard to the relational semantics 'eval_stmt', 
   then there should exist a constant k that statement c starting from 
   s will terminate in state s' within k steps with respect to the 
   functional semantics 'f_eval_stmt';
*)

Ltac apply_rewrite := 
    match goal with
    | h: eval_expr ?s ?e ?s' |- _ => 
        rewrite (f_eval_expr_complete _ _ _ h)
    | h: update _ _ _ = _ |- _ => rewrite h
    | h: f_eval_stmt _ _ _ = _ |- _ => rewrite h
    | h: f_eval_expr _ _ = _ |- _ => rewrite h
    end; auto.

Theorem f_eval_stmt_complete : forall s c s',
        eval_stmt s c s' -> (* s' is either a normal state or a run time error *)
            exists k, f_eval_stmt k s c = s'.
Proof. 
  intros s c s' H;
  induction H;
  try match goal with
  [ h: eval_expr ?s ?e Val_Run_Time_Error |- exists k, _ = S_Run_Time_Error] => 
          exists 1%nat; simpl;
          rewrite (f_eval_expr_complete _ _ _ h);
          reflexivity
  end.
  (* 1. S_Assignment *)
  - exists 1%nat; simpl.
    repeat apply_rewrite.
  (* 2. S_Sequence *)
  - destrIH.
    exists (S k); simpl.
    apply_rewrite.
  - destrIH.
    exists (S (k0+k)); simpl.
    kgreater.
    specialize (eval_stmt_state _ _ _ H0); intros hz1.
    destruct hz1 as [hz2 | hz2]; try rm_exists; subst;
    kgreater.
  (* 3. S_If *)
  - destrIH.
    exists (S k); simpl.
    apply_rewrite.
  - exists 1%nat; simpl.
    apply_rewrite.
  (* 4. S_While_Loop *)
  - destrIH.
    exists (S k); simpl.
    repeat apply_rewrite.
  - destrIH.
    exists (S (k0+k)); simpl.
    apply_rewrite.
    kgreater.
    specialize (eval_stmt_state _ _ _ H1); intros hz1.
    destruct hz1 as [hz2 | hz2]; try rm_exists; subst;
    kgreater.
  - exists 1%nat; simpl.
    apply_rewrite.
Qed.

(**********************************************************************)
(**********************************************************************)

(** * Subprogram Semantics *)

(** In the current SPARK subset, there is no procedure call, 
    so right now we only define the semantics for the main procedure.
    And it can be used to test the tool chain from SPARK source code 
    to Coq evaluation; Later, we will add the procedure call and 
    modify the following procedure semantics;
*)

(** all declared variables in the same procedure should have unique 
    names; 
*)

(** relational (eval_decl) and functional (f_eval_decl) semantics for 
    variable declaration;
*)
Inductive eval_decl: store -> object_declaration -> state -> Prop :=
    | eval_Decl_E: forall e d s,
        Some e = d.(initialization_expression) ->
        eval_expr s e Val_Run_Time_Error ->
        eval_decl s d S_Run_Time_Error
    | eval_Decl: forall d x e v s,
        x = d.(object_name) ->
        Some e = d.(initialization_expression) ->
        eval_expr s e (Val_Normal v) ->
        eval_decl s d (S_Normal ((x, Value v) :: s))
    | eval_UndefDecl: forall d x s,
        x = d.(object_name) ->
        None = d.(initialization_expression) ->
        eval_decl s d (S_Normal ((x, Undefined) :: s)).

Function f_eval_decl (s: store) (d: object_declaration): state :=
    let x := d.(object_name) in
    let e := d.(initialization_expression) in
    match e with
    | Some e' => 
        match f_eval_expr s e' with
        | Val_Normal v => 
            S_Normal ((x, Value v) :: s)
        | Val_Run_Time_Error =>
            S_Run_Time_Error      
        | Val_Abnormal => S_Abnormal 
        end
    | None => S_Normal ((x, Undefined) :: s)
    end.

(** relational (eval_decls) and functional (f_eval_decls) semantics 
    for a sequence of object declarations;
*)
Inductive eval_decls: store -> (list object_declaration) -> state -> Prop :=
    | eval_EmptyDecls: forall s,
        eval_decls s nil (S_Normal s)
    | eval_Decls_E: forall d tl s,
        eval_decl s d S_Run_Time_Error ->
        eval_decls s (d::tl) S_Run_Time_Error
    | eval_Decls: forall d tl s1 s2 s3,
        eval_decl s1 d (S_Normal s2) ->
        eval_decls s2 tl s3 ->
        eval_decls s1 (d::tl) s3.

Function f_eval_decls (s: store) (d: list object_declaration): state :=
    match d with
    | d' :: tl => 
        match f_eval_decl s d' with
        | S_Normal s' => f_eval_decls s' tl 
        | S_Run_Time_Error => S_Run_Time_Error
        | _ => S_Abnormal
        end
    | nil => S_Normal s
    end.

(** for any initial state s, after executing the declaration d, 
    it either returns a normal state s' or a run time error;
    (for any variable declaration, if its initialization expression 
     fails the run time checks, for example division by zero or overflow, 
     then it returns an exception)
*)

Lemma eval_decl_state : forall s d s',
        eval_decl s d s' -> (* s' is either a normal state or a run time error *)
            (exists t, s' = S_Normal t) \/ s' = S_Run_Time_Error.
Proof.
    intros s d s' h.
    induction h;
    try match goal with
    | [ |- (exists t, S_Normal ?t1 = S_Normal t) \/ _ ] => left; exists t1; reflexivity
    | [ |- context [ _ \/ ?A = ?A ] ] => right; reflexivity
    end; auto.
Qed.

Lemma eval_decls_state : forall tl s d s',
        eval_decls s (d :: tl) s' -> (* s' is either a normal state or a run time error *)
            (exists v, s' = S_Normal v) \/ s' = S_Run_Time_Error.
Proof.
    induction tl;
    intros s d s' h1.
  - inversion h1; subst.
    right; auto.
    left; exists s2.
    inversion H4; subst; auto.
  - inversion h1; subst.
    right; auto.
    specialize (IHtl _ _ _ H4).
    destruct IHtl as [IH1 | IH1].
    destruct IH1 as [v IH1].
    left; exists v; auto.
    right; auto.
Qed.

(** f_eval_decl completeness and correctness proofs *)

(** bisimulation proof between f_eval_decl and eval_decl: 
    - f_eval_decl_correct
    - f_eval_decl_complete
*)

Lemma f_eval_decl_correct: forall d s s',
    (f_eval_decl s d = (S_Normal s') -> eval_decl s d (S_Normal s')) /\
    (f_eval_decl s d = S_Run_Time_Error -> eval_decl s d S_Run_Time_Error).
Proof.
    intros d s.
    functional induction (f_eval_decl s d);
    intros; split; intros;
    inversion H; subst.
  - econstructor; auto.
    symmetry in e0; apply e0.
    eapply f_eval_expr_correct1; assumption.
  - econstructor.
    symmetry in e0; apply e0.
    eapply f_eval_expr_correct2; assumption.
  - econstructor; auto.
Qed.

Lemma f_eval_decl_complete: forall d s s',
    eval_decl s d s' ->
    f_eval_decl s d = s'.
Proof.
    intros d s s' h.
    induction h;
    unfold f_eval_decl.
  - rewrite <- H.
    apply f_eval_expr_complete in H0.
    rewrite H0;
    reflexivity.
  - rewrite <- H0.
    apply f_eval_expr_complete in H1.
    rewrite H1.
    rewrite <- H. 
    reflexivity.
  - rewrite <- H0.
    rewrite <- H.
    reflexivity.
Qed.

(** f_eval_decls completeness and correctness proofs *)

(** bisimulation proof between f_eval_decls and eval_decls: 
    - f_eval_decls_correct
    - f_eval_decls_complete
*)

Lemma f_eval_decls_correct: forall d s s',
    (f_eval_decls s d = (S_Normal s') -> 
        eval_decls s d (S_Normal s')) /\
    (f_eval_decls s d = S_Run_Time_Error -> 
        eval_decls s d S_Run_Time_Error).
Proof.
    induction d;
    intros; 
    split; intros.
  - inversion H; subst.
    constructor.
  - inversion H.
  - simpl in H.
    remember (f_eval_decl s a) as b. 
    symmetry in Heqb.
    destruct b; inversion H; subst.
    specialize (IHd s0 s'). destruct IHd as [IH0 IH1].
    specialize (IH0 H).
    econstructor.
    apply f_eval_decl_correct in Heqb.
    apply Heqb.
    rewrite H. assumption.
  - simpl in H.
    remember (f_eval_decl s a) as b;
    symmetry in Heqb.
    destruct b; inversion H; subst.    
    specialize (IHd s0 s0). destruct IHd as [IH0 IH1].
    specialize (IH1 H).
    apply f_eval_decl_correct in Heqb.
    econstructor.
    apply Heqb.
    rewrite H; assumption.
    constructor. 
    apply f_eval_decl_correct in Heqb; auto. 
Qed.

Lemma f_eval_decls_complete: forall d s s',
    eval_decls s d s' ->
    f_eval_decls s d = s'.
Proof.
    intros d s s' h.
    induction h.
  - constructor.
  - apply f_eval_decl_complete in H.
    unfold f_eval_decls.
    rewrite H; auto.
  - apply f_eval_decl_complete in H.
    unfold f_eval_decls.
    rewrite H; auto.
Qed.

(* = = = = = = Subprogram Body = = = = = =  *)
(** relational and functional semantics for procedure body; *)

Inductive eval_proc: store -> procedure_body -> state -> Prop :=
    | eval_Proc_E: forall f s,
        eval_decls s f.(procedure_declarative_part) S_Run_Time_Error ->
        eval_proc s f S_Run_Time_Error
    | eval_Proc: forall f s1 s2 s3,
        eval_decls s1 f.(procedure_declarative_part) (S_Normal s2) ->
        eval_stmt s2 f.(procedure_statements) s3 ->
        eval_proc s1 f s3.

Function f_eval_proc k (s: store) (f: procedure_body): state :=
    match (f_eval_decls s f.(procedure_declarative_part)) with
    | S_Normal s' => f_eval_stmt k s' f.(procedure_statements)
    | S_Run_Time_Error => S_Run_Time_Error
    | _ => S_Abnormal
    end.


(** ** Main Procedure Evaluation Without Parameters *)

(** relational and functional semantics for main procedure; *)

Inductive eval_subprogram: store -> subprogram -> state -> Prop :=
    | eval_Procedure: forall s s' ast_num f,
        eval_proc s f s' ->
        eval_subprogram s (Procedure ast_num f) s'.

Function f_eval_subprogram k (s: store) (f: subprogram): state := 
    match f with 
    | Procedure ast_num f' => f_eval_proc k s f'
    end.

(** ** Bisimulation Between Relational And Functional Semantics For Main Procedure *)

(** *** f_eval_subprogram_correct *)
Theorem f_eval_subprogram_correct: forall k s f s',
    (f_eval_subprogram k s f = S_Normal s' -> 
        eval_subprogram s f (S_Normal s')) /\
    (f_eval_subprogram k s f = S_Run_Time_Error -> 
        eval_subprogram s f S_Run_Time_Error).
Proof.
    intros; 
    split; intros;
    destruct f;
    simpl in H;
    constructor;
    unfold f_eval_proc in H;
    remember (f_eval_decls s (procedure_declarative_part p)) as x;
    symmetry in Heqx.
  - (* normal state *)
    destruct x; inversion H; subst.
    econstructor.
    + apply f_eval_decls_correct in Heqx.
       apply Heqx.
    + apply f_eval_stmt_correct in H.
       rewrite H1; auto.
  - (* run time error *)
    destruct x; inversion H; subst.
    + econstructor.
       * apply f_eval_decls_correct in Heqx.
         apply Heqx.
       * rewrite H.
         apply f_eval_stmt_correct in H; auto.
    + econstructor.
       apply f_eval_decls_correct in Heqx; auto.
Qed.

(** *** f_eval_subprogram_complete *)
Theorem f_eval_subprogram_complete: forall s f s',
    eval_subprogram s f s' ->
    exists k, f_eval_subprogram k s f = s'.
Proof.
    intros s f s' h.
    unfold f_eval_subprogram.
    unfold f_eval_proc.
    inversion h; subst.
    inversion H; subst.
  - apply f_eval_decls_complete in H0.
    rewrite H0. 
    exists 0; auto.
  - apply f_eval_decls_complete in H0.
    rewrite H0.
    apply f_eval_stmt_complete in H1.
    auto.
Qed.

