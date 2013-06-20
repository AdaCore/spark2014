Require Export language.
Require Export values.
Require Export environment.

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

Inductive eval_expr: stack -> expr -> return_val -> Prop :=
    | eval_Econst: forall ast_id cst s v,
        v = eval_constant cst ->
        eval_expr s (Econst ast_id cst) v
    | eval_Evar: forall ast_id v x s,
        Some v = fetch x s ->
        eval_expr s (Evar ast_id x) (ValNormal v)
    | eval_Ebinop: forall ast_id op s e1 e2 v1 v2 v,
        eval_expr s e1 v1 ->
        eval_expr s e2 v2 ->
        ValNormal v = eval_binop op v1 v2 ->
        eval_expr s (Ebinop ast_id op e1 e2) (ValNormal v)
    | eval_Eunop: forall ast_id op s e v b,
        eval_expr s e (ValNormal (Bool b)) ->
        v = eval_unop op (ValNormal (Bool b)) ->
        eval_expr s (Eunop ast_id op e) v.

Inductive eval_stmt: stack -> stmt -> stack -> Prop := 
    | eval_Sassign: forall ast_id s s1 x e v,
        eval_expr s e (ValNormal v) ->
        Some s1 = update s x (Value v) -> (* needs the type check on both sides *)
        eval_stmt s (Sassign ast_id x e) s1
    | eval_Sseq: forall ast_id s s1 s2 c1 c2,
        eval_stmt s c1 s1 ->
        eval_stmt s1 c2 s2 ->
        eval_stmt s (Sseq ast_id c1 c2) s2
    | eval_Sifthen_True: forall ast_id s s1 b c,
        eval_expr s b (ValNormal (Bool true)) ->
        eval_stmt s c s1 ->
        eval_stmt s (Sifthen ast_id b c) s1
    | eval_Sifthen_False: forall ast_id s b c,
        eval_expr s b (ValNormal (Bool false)) ->
        eval_stmt s (Sifthen ast_id b c) s
    | eval_Swhile_True: forall ast_id s s1 s2 b c,
        eval_expr s b (ValNormal (Bool true)) ->
        eval_stmt s c s1 ->
        eval_stmt s1 (Swhile ast_id b c) s2 ->
        eval_stmt s (Swhile ast_id b c) s2
    | eval_Swhile_False: forall ast_id s b c,
        eval_expr s b (ValNormal (Bool false)) ->
        eval_stmt s (Swhile ast_id b c) s.
(*    | eval_Sassert: forall ast_id s e,
        eval_expr s e (ValNormal (Bool true)) -> 
        eval_stmt s (Sassert ast_id e) s. *)

(* - - - - - - - - - - - - - - - - - - - - - - - - - - - -  - - - - - - *)

(* here use 'Function' instead of 'Fixpoint' in order to use tactic 'functional induction (f_eval_expr _ _)' in proofs *)
Function f_eval_expr (s: stack) (e: expr): return_val :=
    match e with
    | Econst _ v => eval_constant v
    | Evar _ x =>
        match (fetch x s) with  (* here we have not considered the variable's mode *)
        | Some v => ValNormal v
        | None => ValException
        end
    | Ebinop _ op e1 e2 =>
        match f_eval_expr s e1 with
        | ValNormal v1 => 
            match f_eval_expr s e2 with
            | ValNormal v2 => eval_binop op (ValNormal v1) (ValNormal v2)
            | _ => ValException
            end
        | _ => ValException
        end   
    | Eunop _ op e => 
        let v := f_eval_expr s e in
        eval_unop op v
    end.

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
            | None => SException
            end
        | ValException => SException
        end
    | Sseq ast_id c1 c2 =>
        match f_eval_stmt k' s c1 with
        | SNormal s1 => f_eval_stmt k' s1 c2
        | SException => SException
        | SUnterminated => SUnterminated
        end
    | Sifthen ast_id b c =>
        match f_eval_expr s b with
        | ValNormal (Bool true) => f_eval_stmt k' s c
        | ValNormal (Bool false) => SNormal s
        | _ => SException
        end
    | Swhile ast_id b c => 
        match f_eval_expr s b with
        | ValNormal (Bool true) => 
            match f_eval_stmt k' s c with
            | SNormal s1 => f_eval_stmt k' s1 (Swhile ast_id b c)
            | SException => SException
            | SUnterminated => SUnterminated
            end
        | ValNormal (Bool false) => SNormal s
        | _ => SException
        end
    end
  end.

(* - - - - - - - - - - - - - - - - - - - - - - - - - - - -  - - - - - - *)
(* Bisumlation between inductive and functional semantics. *)

Lemma f_eval_expr_correct : forall s e v,
                        f_eval_expr s e = ValNormal v ->
                            eval_expr s e (ValNormal v).
Proof.
    intros s e.
    induction e; intros v h.
  - (* 1. Econst *)
    simpl in h; rewrite <- h.
    constructor; reflexivity.
  - (* 2. Evar *)
    constructor.
    simpl in h. destruct (fetch i s); try inversion h.
    reflexivity.
  - (* 3. Ebinop *)
    inversion h; subst.
    remember (f_eval_expr s e1) as v1.
    remember (f_eval_expr s e2) as v2.
    destruct v1; destruct v2; try (inversion H0).
    rewrite H0. econstructor; intuition.
  - (* 4. Eunop *)
    inversion h; subst.
    unfold eval_unop in H0. destruct u.
    remember (f_eval_expr s e) as v1.
    destruct v1; try (inversion H0).
    destruct v0; try (inversion H1).
    subst.
    specialize (IHe (Bool b)). intuition.
    econstructor; intuition. assumption.
Qed.

Lemma f_eval_expr_complete : forall e s v,  
                        eval_expr e s v -> 
                            (f_eval_expr e s) = v.
Proof.
    intros e s v h.
    induction h; simpl; intros;
    repeat match goal with
    | h: _ = fetch _ _  |- _ => progress rewrite <- h
    | h: f_eval_expr _ _ = _ |- _ => progress rewrite h
    end;auto.
  - destruct v1; destruct v2;
    symmetry;
    [assumption | | | ]; 
    destruct op in H; simpl in H; assumption.
Qed.

(*
Lemma eval_expr_correct : forall s e v,
(*                           correct_stack s -> *)
                          eval_expr e s v ->
                              (exists v1, v = ValNormal v1) \/ v = ValException.
Proof.
  intros s e v h.
  inversion h; auto.
Qed.
*)

(* Bisimulation for semantics of commands. *)
Ltac blam :=
  match goal with
    | H:SUnterminated _ = SNormal _ |- _ => inversion H
    | H:SException = SNormal _ |- _ => inversion H
    | H:SNormal _ = SNormal _ |- _ => inversion H;clear H;subst 
    | h:update _ _ (Value _) = _ |- _ => rewrite h
    | H : f_eval_stmt _ _ _ = _ |- _ => rewrite H
    | H : f_eval_expr _ _ = _ |- _ => rewrite H
  end;subst;simpl;auto.

Ltac invle := match goal with
    | H: (S _ <= _)%nat |- _ => (inversion H; clear H; subst;simpl)
  end.


Lemma f_eval_stmt_fixpoint: forall s p (k:nat) s', 
        f_eval_stmt k s p = SNormal s' ->
        forall k':nat, (k <= k')%nat -> 
            f_eval_stmt k' s p = SNormal s'.
Proof.
    intros s p k.
    functional induction (f_eval_stmt k s p); simpl; intros; subst; simpl; auto;
    repeat progress blam.
  - inversion H.
  - invle.
    + repeat blam.
    + blam. blam.
  - invle.
    + repeat blam.
    + rewrite (IHs0 _ e1);auto with arith.
  - inversion H.
  - invle; repeat blam. rewrite (IHs0 _ H);auto with arith.
  - invle; repeat blam.
  - invle; repeat blam. rewrite (IHs0 _ e2); auto with arith.
  - inversion H.
  - invle; repeat blam.
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
         end.




(** Bisimulation between the inductive semantic of commands and the
    executable one. One needs a weak form of type preservation: well
    formedness (that is: no Anomaly or Constraint_error is stored in
    the stack) of the stack is preserved. *)
Lemma f_eval_stmt_correct : forall s p s',
        eval_stmt s p s' ->
            exists k, f_eval_stmt k s p = SNormal s'.
Proof.
  intros s p s' H.
  induction H.
  - exists 1%nat. simpl.
    rewrite (f_eval_expr_complete _ _ _ H).
    rewrite <- H0. 
    reflexivity.
  - destrIH.
    exists (S (k0+k)).
    simpl.
    kgreater.
  - destrIH.
    exists (S (k)).
    simpl.
    rewrite (f_eval_expr_complete _ _ _ H).
    assumption.
(*  - destrIH.
    exists (S (k)).
    simpl.
    rewrite <- (feval_complete _ _ _ H).
    assumption.*)
  - exists (S 0).
    simpl.
    rewrite (f_eval_expr_complete _ _ _ H).
    reflexivity.
  - destrIH.
    exists (S (k0+k)).
    simpl.
    kgreater.
    rewrite (f_eval_expr_complete _ _ _ H).
    reflexivity.
  - exists (S 0).
    simpl.
    rewrite (f_eval_expr_complete _ _ _ H).
    reflexivity.
Qed.

Lemma f_eval_stmt_complete : forall k s p s',
        f_eval_stmt k s p = SNormal s' ->
          eval_stmt s p s'.
Proof.
    intros k s p.
    functional induction (f_eval_stmt k s p); 
    intros s' H; try inversion H.
  - (* Sassign *)
    eapply eval_Sassign. 
    apply f_eval_expr_correct in e2. apply e2.
    blam.
  - (* Sseq *)
    eapply eval_Sseq. 
    specialize (IHs0 s1 e1).
    apply IHs0. 
    specialize (IHs1 s' H).
    apply IHs1.
  - (* Cifthen_True *)
    eapply eval_Sifthen_True.
    apply f_eval_expr_correct in e1. assumption.
    specialize (IHs0 s' H). assumption.
  - (* Cifthen_False *)
    eapply eval_Sifthen_False.
    apply f_eval_expr_correct in e1. 
    subst. assumption.
  - (* Swhile_True *)
    eapply eval_Swhile_True.
    apply f_eval_expr_correct in e1. assumption.
    specialize (IHs0 s1 e2). apply IHs0.
    specialize (IHs1 s' H). assumption.
  - (* Swhile_False *)
    eapply eval_Swhile_False.
    apply f_eval_expr_correct in e1. 
    subst; assumption.
Qed.
    

(* - - - - - - - - - - - - - - - - - - - - - - - - - - - -  - - - - - - *)
(* basic lemmas *)
Lemma expr_type_infer: forall op v1 v2 n,
    eval_binop op v1 v2 = ValNormal (Int n) -> (exists n1 n2, v1 = ValNormal (Int n1) /\ v2 = ValNormal (Int n2)).
Proof.
    intros.
    unfold eval_binop in H. 
    destruct v1 as [v1' | ]; 
    destruct v2 as [v2' | ];
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
    destruct v1 as [v1' | ]; 
    destruct v2 as [v2' | ]; 
    destruct op; 
    simpl in H; try inversion H;
    destruct v1'; 
    destruct v2';
    simpl in H; try inversion H.
    left; exists n0, n1; auto.
    left; exists n0, n1; auto.
    right; exists b, b0; auto.
    right; exists b, b0; auto.
Qed.







