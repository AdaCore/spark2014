Require Export values.
Require Export environment.
Require Import util.

(** * Relational Semantics *)
(** interpret the constant syntax as a constant stored value *)
Definition eval_constant (cst: constant): value :=
    match cst with
    | Ointconst v => (Int v)
    | Oboolconst b => (Bool b)
    end.
(*
Inductive eval_const: constant -> value -> Prop :=
    | C_Int: forall v, 
        eval_const (Ointconst v) (Int v)
    | C_Bool: forall b, 
        eval_const (Oboolconst b) (Bool b).
*)

(** interpret the binary operation for each binary operator *)
Inductive eval_binexpr: binary_operation -> value -> value -> value -> Prop :=
    | Eq: forall v1 v2 b,
        Zeq_bool v1 v2 = b ->
        eval_binexpr Ceq (Int v1) (Int v2) (Bool b)
    | Ne: forall v1 v2 b,
        Zneq_bool v1 v2 = b ->
        eval_binexpr Cne (Int v1) (Int v2) (Bool b)
    | And: forall v1 v2 b,
        andb v1 v2 = b ->
        eval_binexpr Oand (Bool v1) (Bool v2) (Bool b)
    | Or: forall v1 v2 b,
        orb v1 v2 = b ->
        eval_binexpr Oor (Bool v1) (Bool v2) (Bool b)
    | Add: forall v1 v2 v3,
        (v1 + v2)%Z =v3 ->
        eval_binexpr Oadd (Int v1) (Int v2) (Int v3)
    | Sub: forall v1 v2 v3,
        (v1 - v2)%Z =v3 ->
        eval_binexpr Osub (Int v1) (Int v2) (Int v3)
    | Mul: forall v1 v2 v3,
        (v1 * v2)%Z =v3 ->
        eval_binexpr Omul (Int v1) (Int v2) (Int v3)
    | Div: forall v1 v2 v3,
        (v1 / v2)%Z =v3 ->
        eval_binexpr Odiv (Int v1) (Int v2) (Int v3).

(** interpret the unary operation *)
Inductive eval_unaryexpr : unary_operation -> value -> value -> Prop :=
    | Not: forall b v,
        negb b = v ->
        eval_unaryexpr Onot (Bool b) (Bool v).

Lemma eval_bin_unique: forall op v1 v2 x y,
    eval_binexpr op v1 v2 x ->
    eval_binexpr op v1 v2 y ->
    x = y.
Proof.
    intros.
    destruct op;
    inversion H; subst; inversion H0; subst;
    auto.
Qed.

Lemma eval_unary_unique: forall uop v x y,
    eval_unaryexpr uop v x ->
    eval_unaryexpr uop v y ->
    x = y.
Proof.
    intros.
    destruct uop;
    inversion H; subst; inversion H0; subst;
    auto.
Qed.

(* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - *)
    
(** ** Run-Time Checking Rules *)
(** *** check rules marking what and where to check *)
(** 
      - Do_Division_Check
       
       This flag is set on a division operator (/ mod rem) to indicate
       that a zero divide check is required. 

     - Do_Overflow_Check

       This flag is set on an operator where an overflow check is required on
       the operation.
*)

(** *** check actions *)
(** which are needed to be performed before excecuting the program *)
Inductive check_action: Type := 
   | Do_Division_Check: check_action
   | Do_Overflow_Check: check_action.

(** add check flags for AST nodes according to the checking rules *)
Inductive check_flag: expr -> option check_action -> Prop :=
    | CF_Econst_Int: forall ast_num n,
        check_flag (Econst ast_num (Ointconst n)) None
    | CF_Econst_Bool: forall ast_num b,
        check_flag (Econst ast_num (Oboolconst b)) None
    | CF_Evar: forall ast_num x,  
        check_flag (Evar ast_num x) None
    | CF_Ebinop_Div: forall ast_num e1 e2,
        check_flag (Ebinop ast_num Odiv e1 e2) (Some Do_Division_Check)
    | CF_Ebinop_Others: forall ast_num op e1 e2,
        op <> Odiv ->
        check_flag (Ebinop ast_num op e1 e2) None
    | CF_Eunop: forall ast_num op e,
        check_flag (Eunop ast_num op e) None.

(** *** semantics for run-time checks *)

Inductive is_not_zero: Z -> bool -> Prop :=
    | Not_Zero: forall v, v <> 0%Z -> is_not_zero v true
    | Is_Zero: forall v, v = 0%Z -> is_not_zero v false.

Inductive do_check: binary_operation -> value -> value -> bool -> Prop :=
    | Do_Division_Check0: forall v1 v2 b,
        is_not_zero v2 b ->
        do_check Odiv v1 (Int v2) b
    | Do_Nothing: forall op v1 v2,
        op <> Odiv ->
        do_check op v1 v2 true.
(*
    | DC_Overflow_Check0: 
    | ... 
*)

(** ** Expression semantics *)
(**
    for binary expression and unary expression, if any of its child expression returns exception,
    then the reuslt of the whole expression is exception; for binary expression (e1 op e2), 
    if both e1 and e2 can evaluate to some normal value, then we do some checks on the operator 'op',
    whenever the check fails, an exception is returned, otherwise, binary operation result is returned
 *)
Inductive eval_expr: stack -> expr -> return_val -> Prop :=
    | eval_Econst: forall cst v s ast_num,
        eval_constant cst = v ->
        eval_expr s (Econst ast_num cst) (ValNormal v)
    | eval_Evar: forall x s v ast_num,
        fetch x s = Some v ->
        eval_expr s (Evar ast_num x) (ValNormal v)
    | eval_Ebinop1: forall s e1 ast_num op e2,
        eval_expr s e1 ValException ->
        eval_expr s (Ebinop ast_num op e1 e2) ValException
    | eval_Ebinop2: forall s e1 v1 e2 ast_num op,
        eval_expr s e1 (ValNormal v1) ->
        eval_expr s e2 ValException ->
        eval_expr s (Ebinop ast_num op e1 e2) ValException
    | eval_Ebinop3: forall s e1 v1 e2 v2 ast_num op,
        eval_expr s e1 (ValNormal v1) ->
        eval_expr s e2 (ValNormal v2) ->
        do_check op v1 v2 false ->
        eval_expr s (Ebinop ast_num op e1 e2) ValException
    | eval_Ebinop4: forall s e1 v1 e2 v2 ast_num op v,
        eval_expr s e1 (ValNormal v1) ->
        eval_expr s e2 (ValNormal v2) ->
        do_check op v1 v2 true ->
        eval_binexpr op v1 v2 v ->
        eval_expr s (Ebinop ast_num op e1 e2) (ValNormal v)
    | eval_Eunop1: forall s e ast_num op,
        eval_expr s e ValException ->
        eval_expr s (Eunop ast_num op e) ValException
    | eval_Eunop2: forall s e v ast_num op v1,
        eval_expr s e (ValNormal v) ->
        eval_unaryexpr op v v1 ->
        eval_expr s (Eunop ast_num op e) (ValNormal v1).


(** ** Statement semantics *)
(** 
   for any command, whenever its sub-command throws an exception or any expression 
   evaluate to an exception, then the whole command returns an exception; 
*)
Inductive eval_stmt: stack -> stmt -> state -> Prop := 
    | eval_Sassign1: forall s e ast_num x,
        eval_expr s e ValException ->
        eval_stmt s (Sassign ast_num x e) SException
    | eval_Sassign2: forall s e v x s1 ast_num,
        eval_expr s e (ValNormal v) ->
        update s x (Value v) = Some s1 ->
        eval_stmt s (Sassign ast_num x e) (SNormal s1)
    | eval_Sseq1: forall s c1 ast_num c2,
        eval_stmt s c1 SException ->
        eval_stmt s (Sseq ast_num c1 c2) SException
    | eval_Sseq2: forall ast_num s s1 s2 c1 c2,
        eval_stmt s c1 (SNormal s1) ->
        eval_stmt s1 c2 s2 ->
        eval_stmt s (Sseq ast_num c1 c2) s2
    | eval_Sifthen: forall s b ast_num c,
        eval_expr s b ValException ->
        eval_stmt s (Sifthen ast_num b c) SException
    | eval_Sifthen_True: forall s b c s1 ast_num,
        eval_expr s b (ValNormal (Bool true)) ->
        eval_stmt s c s1 ->
        eval_stmt s (Sifthen ast_num b c) s1
    | eval_Sifthen_False: forall s b ast_num c,
        eval_expr s b (ValNormal (Bool false)) ->
        eval_stmt s (Sifthen ast_num b c) (SNormal s)
    | eval_Swhile: forall s b ast_num c,
        eval_expr s b ValException ->
        eval_stmt s (Swhile ast_num b c) SException
    | eval_Swhile_True1: forall s b c ast_num,
        eval_expr s b (ValNormal (Bool true)) ->
        eval_stmt s c SException ->
        eval_stmt s (Swhile ast_num b c) SException
    | eval_Swhile_True2: forall s b c s1 ast_num s2,
        eval_expr s b (ValNormal (Bool true)) ->
        eval_stmt s c (SNormal s1) ->
        eval_stmt s1 (Swhile ast_num b c) s2 ->
        eval_stmt s (Swhile ast_num b c) s2
    | eval_Swhile_False: forall s b ast_num c,
        eval_expr s b (ValNormal (Bool false)) ->
        eval_stmt s (Swhile ast_num b c) (SNormal s).

(* - - - - - - - - - - - - - - - - - - - - - - - - - - - -  - - - - - - *)

(** * Functional Semantics *)

Function f_do_check (op: binary_operation) (v1: value) (v2: value): option bool :=
    match op with
    | Odiv =>
        match v2 with
        | Int v2' => if Zeq_bool v2' 0 then Some false else Some true
        | _ => None
        end
    | _ => Some true
    end.

(** interpret the binary operation for each binary operator *)
Definition f_eval_binexpr (op: binary_operation) (v1: value) (v2: value): return_val :=
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

(** interpret the unary operation *)
Definition f_eval_unaryexpr (op: unary_operation) (v: value): return_val :=
    match op with
    | Onot => Val.not v
    end.

(** ** Expression semantics *)

(**
    in functional semantics for expression, it can return a normal value or an exception or 
    go abnormal, the checks are encoded inside the semantics
*)
(* here use 'Function' instead of 'Fixpoint' in order to use 
   tactic 'functional induction (f_eval_expr _ _)' in proofs *)
Function f_eval_expr (s: stack) (e: expr): return_val :=
    match e with
    | Econst _ v => ValNormal (eval_constant v)
    | Evar _ x =>
        match (fetch x s) with  (* here we have not considered the variable's mode *)
        | Some v => ValNormal v
        | None => ValAbnormal
        end
    | Ebinop _ op e1 e2 =>
        match f_eval_expr s e1 with
        | ValNormal v1 => 
            match f_eval_expr s e2 with
            | ValNormal v2 => 
                match f_do_check op v1 v2 with
                | Some true => f_eval_binexpr op v1 v2
                | Some false => ValException
                | _ => ValAbnormal
                end
            | ValException => ValException
            | ValAbnormal => ValAbnormal
            end
        | ValException => ValException
        | ValAbnormal => ValAbnormal
        end   
    | Eunop _ op e => 
        match f_eval_expr s e with
        | ValNormal v => f_eval_unaryexpr op v
        | ValException => ValException
        | ValAbnormal => ValAbnormal
        end
    end.

(** ** Statement semantics *)
(** 
   in the functional semantics for command, 'k' denotes the execution steps, whenever it reaches 0,
   an untermination state is returned, in other cases, it can return a normal state, an exception or
   an abnormal state; checks are encoded inside the functional semantics
*)
Function f_eval_stmt k (s: stack) (c: stmt) {struct k}: state := 
  match k with
  | 0 => SUnterminated
  | S k' => 
    match c with
    | Sassign ast_num x e =>
        match f_eval_expr s e with (* exceptions maybe raised either in evaluation of e or when looking up x  *)
        | ValNormal v => 
            match update s x (Value v) with
            | Some s1 => SNormal s1
            | None => SAbnormal
            end
        | ValException => SException
        | ValAbnormal => SAbnormal
        end
    | Sseq ast_num c1 c2 =>
        match f_eval_stmt k' s c1 with
        | SNormal s1 => f_eval_stmt k' s1 c2
        | SException => SException
        | SUnterminated => SUnterminated
        | SAbnormal => SAbnormal
        end
    | Sifthen ast_num b c =>
        match f_eval_expr s b with
        | ValNormal (Bool true) => f_eval_stmt k' s c
        | ValNormal (Bool false) => SNormal s
        | ValException => SException
        | _ => SAbnormal
        end
    | Swhile ast_num b c => 
        match f_eval_expr s b with
        | ValNormal (Bool true) => 
            match f_eval_stmt k' s c with
            | SNormal s1 => f_eval_stmt k' s1 (Swhile ast_num b c)
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

(*
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
    destruct (Zeq_bool n0 0); inversion H.
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
    destruct (Zeq_bool n0 0); inversion H.
Qed.
*)

(* - - - - - - - - - - - - - - - - - - - - - - - - - - - -  - - - - - - *)

(** * Bisimulation Between Relational And Functional Semantics *)

(** for any expression e, if it evaluate to v1 and v2, then v1 and v2 should be the same *)
Lemma eval_expr_unique: forall s e v1 v2,
    eval_expr s e (ValNormal v1) ->
    eval_expr s e (ValNormal v2) ->
    v1 = v2.
Proof.
    induction e; 
    intros v1 v2 h1 h2;
    inversion h1; subst; 
    inversion h2; subst.
  - auto.
  - rewrite H1 in H2; inversion H2; auto.
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
    for any expression e evaluated under the state s, if it can be evaluated to a value v 
    under the relational semantics, then the result value v should be either a normal value or exception.
*)
Lemma eval_expr_state : forall s e v,
        eval_expr s e v ->                        (* s' is either a normal state or an exception *)
            (exists v0, v = ValNormal v0) \/ v = ValException.
Proof.
    intros s e v h.
    induction h;
    try match goal with
    | [ |- (exists v, ValNormal ?v1 = ValNormal v) \/ _ ] => left; exists v1; reflexivity
    | [ |- context [ _ \/ ?A = ?A ] ] => right; reflexivity
    end; auto.
Qed.

(** 
    for any statement c run under the state s, if it can execute to a state s' under the relational
    semantics, then the result state s' should be either a normal state or exception. In our relational 
    semantics, all commands that can go abnormal are excluded
*)
Lemma eval_stmt_state : forall s c s',
        eval_stmt s c s' ->                        (* s' is either a normal state or an exception *)
            (exists v, s' = SNormal v) \/ s' = SException.
Proof.
    intros s c s' h.
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

Lemma f_do_check_correct: forall op v1 v2 b,
    f_do_check op v1 v2 = Some b ->
    do_check op v1 v2 b.
Proof.
    intros op v1 v2;
    functional induction (f_do_check op v1 v2);
    intros b h1;
    inversion h1; subst.
  - constructor.
    apply Zeq_zero_true.
    assumption.
  - constructor.
    apply Zeq_zero_false.
    assumption.
  - destruct op; try inversion y;
    constructor; unfold not; intros hz1;
    inversion hz1.
Qed.

Lemma f_do_check_complete: forall op v1 v2 b,
    do_check op v1 v2 b ->
    f_do_check op v1 v2 = Some b.
Proof.
    intros op v1 v2 b h1.
    induction h1.
  - simpl.
    destruct b.
    specialize (Zeq_zero_false v2); intros hz1.
    destruct hz1 as [hz1 hz2].
    specialize (hz2 H).
    rewrite hz2; auto.
    specialize (Zeq_zero_true v2); intros hz1.
    destruct hz1 as [hz1 hz2].
    specialize (hz2 H).
    rewrite hz2; auto.
  - destruct op; intuition.
Qed.

Lemma f_eval_binexpr_correct: forall op v1 v2 v,
    f_eval_binexpr op v1 v2 = ValNormal v ->
    eval_binexpr op v1 v2 v.
Proof.
    intros op v1 v2 v h1.
    destruct op;
    match goal with 
    |[|- eval_binexpr Odiv _ _ _] => idtac
    |[|- eval_binexpr ?op _ _ _] =>
        destruct v1, v2;
        simpl in h1; inversion h1; subst;
        constructor; auto
    end.
    destruct v1, v2; simpl in h1; inversion h1.
    constructor.
    remember (Zeq_bool n0 0) as x.
    reflexivity.
Qed.

Lemma f_eval_binexpr_complete: forall op v1 v2 v,
    eval_binexpr op v1 v2 v ->
    f_eval_binexpr op v1 v2 = ValNormal v.
Proof.
    intros op v1 v2 v h1.
    induction h1;
    rewrite <- H;
    simpl; auto.
Qed.

Lemma f_eval_unaryexpr_correct: forall op v v',
    f_eval_unaryexpr op v = ValNormal v' ->
    eval_unaryexpr op v v'.
Proof.
    intros.
    destruct op; simpl in H.
    destruct v; inversion H; subst.
    constructor; auto.
Qed.

Lemma f_eval_unaryexpr_complete: forall op v v',
    eval_unaryexpr op v v' ->
    f_eval_unaryexpr op v = ValNormal v'.
Proof.
    intros op v v' h1;
    induction h1;
    rewrite <- H;
    simpl; auto.
Qed.

(** ** Semantics equivalence for expression *)
(** a help lemma to prove the theorem: f_eval_expr_correct *)
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
    rewrite H0.
    econstructor.
    exact IHr. exact IHr0.
    + apply f_do_check_correct.
      auto.
    + apply f_eval_binexpr_correct; 
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
                        f_eval_expr s e = ValException ->
                            eval_expr s e ValException.
Proof.
    intros s e.
    functional induction (f_eval_expr s e);
    intros h; try inversion h.
  - destruct op, v1, v2;
    simpl in h; inversion h.
  - specialize (f_eval_expr_correct1 _ _ _ e3); intros hz1.
    specialize (f_eval_expr_correct1 _ _ _ e4); intros hz2.
    eapply eval_Ebinop3.
    apply hz1. apply hz2.
    apply f_do_check_correct; auto.
  - specialize (f_eval_expr_correct1 _ _ _ e3); intros hz1.
    specialize (IHr0 e4).
    eapply eval_Ebinop2; auto.
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
    for any expression e evaluated with 'f_eval_expr' under the state s,  whenever it returns 
    a normal value v or an exception, the relationship between evaluation result, s and e should 
    also be satisfied with regard to the relational semantics 'eval_expr'
*)
Theorem f_eval_expr_correct : forall s e v,
                        (f_eval_expr s e = ValNormal v ->
                            eval_expr s e (ValNormal v)) /\
                        (f_eval_expr s e = ValException ->
                            eval_expr s e ValException).
Proof.
    split.
  - apply f_eval_expr_correct1.
  - apply f_eval_expr_correct2.
Qed.


(** *** f_eval_expr_complete *)
(** 
   for any expression e, if it can be evaluated to value v under state s with regard to the 
   relational semantics 'eval_expr', then when we evalute e under the same state s in functional
   semantics 'f_eval_expr', it should return the same result v
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
    inversion H; subst. 
    apply Zeq_zero_false in H2. 
    rewrite H2; auto.
    unfold not in H1; intuition.
  - destruct op.
    inversion H; subst.
    auto.
Qed.


Ltac apply_inv :=
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
    | H:update _ _ (Value _) = _ |- _ => rewrite H
    | H:f_eval_stmt _ _ _ = _ |- _ => rewrite H
    | H:f_eval_expr _ _ = _ |- _ => rewrite H
  end;subst;simpl;auto.

Ltac invle := match goal with
    | H: (S _ <= _)%nat |- _ => (inversion H; clear H; subst; simpl)
  end.

(** a help lemma to prove the theorem: 'f_eval_stmt_complete' *)
Lemma f_eval_stmt_fixpoint: forall k s p s', 
        f_eval_stmt k s p = SNormal s' ->
        forall k':nat, (k <= k')%nat -> 
            f_eval_stmt k' s p = SNormal s'.
Proof.
    intros k s p.
    functional induction (f_eval_stmt k s p); simpl; intros; subst; simpl; auto;
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
        f_eval_stmt k s p = SException ->
        forall k':nat, (k <= k')%nat -> 
            f_eval_stmt k' s p = SException.
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

(** a help lemma to prove the theorem: 'f_eval_stmt_complete' *)
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
    apply_inv.
  - (* Cifthen_True *)
    specialize (IHs0 _ H).
    econstructor.
    rm_f_eval_expr. 
    apply_inv.
  - (* Cifthen_False *)
    eapply eval_Sifthen_False.
    rm_f_eval_expr.
  - (* Swhile_True *)
    specialize (IHs0 _ e2).
    specialize (IHs1 _ H).
    econstructor.
    rm_f_eval_expr.
    apply IHs0. 
    apply_inv.
  - (* Swhile_False *)
    eapply eval_Swhile_False.
    rm_f_eval_expr.
Qed.

Ltac rm_f_eval_stmt :=
    match goal with 
    | [ h: f_eval_stmt ?k ?s ?c = SNormal ?s1 |- _ ] => specialize (f_eval_stmt_correct1 _ _ _ _ h); intros hz1
    end; auto.

(** a help lemma to prove the theorem: 'f_eval_stmt_complete' *)
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
    apply_inv.
  - specialize (IHs0 e1).
    econstructor.
    assumption.    
  - (* Cifthen *)
    specialize (IHs0 H).
    econstructor.
    rm_f_eval_expr.
    apply_inv.
  - econstructor.
    specialize (f_eval_expr_correct2 _ _ e1); intros hz1. 
    assumption.
  - (* Swhile *)
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
    | [ h: f_eval_expr ?s ?b = ValException |- _ ] => specialize (f_eval_expr_correct2 _ _ h); intros hz1
    | [ h: f_eval_expr ?s ?b = ValNormal ?v |- _ ] => specialize (f_eval_expr_correct1 _ _ _ h); intros hz1   
    | [ h: f_eval_stmt ?k ?s ?c = SException |- _ ] => specialize (f_eval_stmt_correct2 _ _ _ h); intros hz1
    | [ h: f_eval_stmt ?k ?s ?c = SNormal ?s1 |- _ ] => specialize (f_eval_stmt_correct1 _ _ _ _ h); intros hz1
    end; auto.

(** *** f_eval_stmt_correct *)
(** 
   for any command c, if it returns a normal state or an exception within k steps under the state s 
   with regard to the functional semantics 'f_eval_stmt', then the relationship between s, e and the
   resulting state should also be satisfied with regard to the relational semantics 'eval_stmt'
*)
Theorem f_eval_stmt_correct : forall k s c s',
        (f_eval_stmt k s c = SNormal s' ->
          eval_stmt s c (SNormal s')) /\ 
        (f_eval_stmt k s c = SException ->
          eval_stmt s c SException).
Proof.
    intros.
    split; intros;
    rm_f_eval.
Qed.

(** *** f_eval_stmt_complete *)
(** 
   the reverse direction is also satisfied: for any command c, whenever it's executed under the
   state s and return a new state s' with regard to the relational semantics 'eval_stmt', then
   there should exist a constant k that command c starting from s will terminate in state s' 
   within k steps with regard to the functional semantics 'f_eval_stmt'
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
        eval_stmt s c s' ->                        (* s' is either a normal state or an exception *)
            exists k, f_eval_stmt k s c = s'.
Proof. 
  intros s c s' H;
  induction H;
  try match goal with
  [ h: eval_expr ?s ?e ValException |- exists k, _ = SException] => 
          exists 1%nat; simpl;
          rewrite (f_eval_expr_complete _ _ _ h);
          reflexivity
  end.
  (* 1. Sassign *)
  - exists 1%nat; simpl.
    repeat apply_rewrite.
  (* 2. Sseq *)
  - destrIH.
    exists (S k); simpl.
    apply_rewrite.
  - destrIH.
    exists (S (k0+k)); simpl.
    kgreater.
    specialize (eval_stmt_state _ _ _ H0); intros hz1.
    destruct hz1 as [hz2 | hz2]; try rm_exists; subst;
    kgreater.
  (* 3. Sifthen *)
  - destrIH.
    exists (S k); simpl.
    apply_rewrite.
  - exists 1%nat; simpl.
    apply_rewrite.
  (* 4. Swhile *)
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
     And it can be used to test the tool chain from Ada source code to Coq evaluation;
     
     Later, we will and the procedure call and modify the following procedure semantics.
*)

(** all declared variables have unique names; *)

Inductive eval_decl: stack -> local_declaration -> state -> Prop :=
    | eval_Decl_E: forall e d s,
        Some e = d.(local_init) ->
        eval_expr s e ValException ->
        eval_decl s d SException
    | eval_Decl: forall d x e v s,
        x = d.(local_ident) ->
        Some e = d.(local_init) ->
        eval_expr s e (ValNormal v) ->
        eval_decl s d (SNormal ((x, Value v) :: s))
    | eval_UndefDecl: forall d x s,
        x = d.(local_ident) ->
        None = d.(local_init) ->
        eval_decl s d (SNormal ((x, Vundef) :: s)).

Function f_eval_decl (s: stack) (d: local_declaration): state :=
    let x := d.(local_ident) in
    let e := d.(local_init) in
    match e with
    | Some e' => 
        match f_eval_expr s e' with
        | ValNormal v => 
            SNormal ((x, Value v) :: s)
        | ValException =>
            SException      
        | ValAbnormal => SAbnormal 
        end
    | None => SNormal ((x, Vundef) :: s)
    end.

Inductive eval_decls: stack -> (list local_declaration) -> state -> Prop :=
    | eval_EmptyDecls: forall s,
        eval_decls s nil (SNormal s)
    | eval_Decls_E: forall d tl s,
        eval_decl s d SException ->
        eval_decls s (d::tl) SException
    | eval_Decls: forall d tl s1 s2 s3,
        eval_decl s1 d (SNormal s2) ->
        eval_decls s2 tl s3 ->
        eval_decls s1 (d::tl) s3.

Function f_eval_decls (s: stack) (d: list local_declaration): state :=
    match d with
    | d' :: tl => 
        match f_eval_decl s d' with
        | SNormal s' => f_eval_decls s' tl 
        | SException => SException
        | _ => SAbnormal
        end
    | nil => SNormal s
    end.

Lemma eval_decl_state : forall s d s',
        eval_decl s d s' -> (* s' is either a normal state or an exception *)
            (exists v, s' = SNormal v) \/ s' = SException.
Proof.
    intros s d s' h.
    induction h;
    try match goal with
    | [ |- (exists v, SNormal ?v1 = SNormal v) \/ _ ] => left; exists v1; reflexivity
    | [ |- context [ _ \/ ?A = ?A ] ] => right; reflexivity
    end; auto.
Qed.

Lemma eval_decls_state : forall tl s d s',
        eval_decls s (d :: tl) s' -> (* s' is either a normal state or an exception *)
            (exists v, s' = SNormal v) \/ s' = SException.
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

Lemma f_eval_decl_correct: forall d s s',
    (f_eval_decl s d = (SNormal s') -> eval_decl s d (SNormal s')) /\
    (f_eval_decl s d = SException -> eval_decl s d SException).
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

Lemma f_eval_decls_correct: forall d s s',
    (f_eval_decls s d = (SNormal s') -> eval_decls s d (SNormal s')) /\
    (f_eval_decls s d = SException -> eval_decls s d SException).
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

Inductive eval_proc: stack -> procedure_body -> state -> Prop :=
    | eval_Proc_E: forall f s,
        eval_decls s f.(proc_loc_idents) SException ->
        eval_proc s f SException
    | eval_Proc: forall f s1 s2 s3,
        eval_decls s1 f.(proc_loc_idents) (SNormal s2) ->
        eval_stmt s2 f.(proc_body) s3 ->
        eval_proc s1 f s3.

Function f_eval_proc k (s: stack) (f: procedure_body): state :=
    match (f_eval_decls s f.(proc_loc_idents)) with
    | SNormal s' => f_eval_stmt k s' f.(proc_body)
    | SException => SException
    | _ => SAbnormal
    end.


(** ** Main Procedure Evaluation Without Parameters *)

Inductive eval_subprogram: stack -> subprogram -> state -> Prop :=
    | eval_SubpProc: forall s s' ast_num f,
        eval_proc s f s' ->
        eval_subprogram s (Sproc ast_num f) s'.

Function f_eval_subprogram k (s: stack) (f: subprogram): state := 
    match f with 
    | Sproc ast_num f' => f_eval_proc k s f'
    end.

(** ** Bisimulation Between Relational And Functional Semantics For Main Procedure *)

(** *** f_eval_subprogram_correct *)

Theorem f_eval_subprogram_correct: forall k s f s',
    (f_eval_subprogram k s f = SNormal s' -> eval_subprogram s f (SNormal s')) /\
    (f_eval_subprogram k s f = SException -> eval_subprogram s f SException).
Proof.
    intros; 
    split; intros;
    destruct f;
    simpl in H;
    constructor;
    unfold f_eval_proc in H;
    remember (f_eval_decls s (proc_loc_idents p)) as x;
    symmetry in Heqx.
  - (* normal state *)
    destruct x; inversion H; subst.
    econstructor.
    + apply f_eval_decls_correct in Heqx.
       apply Heqx.
    + apply f_eval_stmt_correct in H.
       rewrite H1; auto.
  - (* exception *)
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




