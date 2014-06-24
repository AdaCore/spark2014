Require Export language.

(** * Run Time Checks *)
(** a subset of run time checks to be verified *)
(**
     - Division Check
       
       Check that the second operand of the the division, mod or rem 
       operation is different from zero.

     - Overflow Check

       Check that the result of the given arithmetic operation is within 
       the bounds of the base type.

     - Index Check
       
       Check that the given index is within the bounds of the array.
     
     - Range Check
       
       Check that the given value is within the bounds of the expected scalar 
       subtype.
*)

(** ** Run Time Check Flags *)
(** checks that are needed to be verified at run time *)
Inductive check_flag: Type := 
    | Do_Division_Check: check_flag
    | Do_Overflow_Check: check_flag
    | Do_Index_Check:    check_flag.   (* index check for an array access *)
(*  | Do_Range_Check:    check_flag *) (* range check for a scalar range, e.g. -1 is assigned to natural variable *) 


(** For an expression or statement, there may exists a list of checks 
    enforced on it, for example, for division expression, both
    division by zero and overflow checks are needed to be performed;
*)
Definition check_flags := list check_flag.

(** produce check flags for expressions according to the checking rules; 
    it is a mapping from one ast node to a set of run time checks;
*)

(** ** Run Time Check Flags Generator *)

Inductive gen_check_flags: expression -> check_flags -> Prop :=
    | GCF_Literal_Int: forall ast_num n,
        gen_check_flags (E_Literal ast_num (Integer_Literal n)) nil
    | GCF_Literal_Bool: forall ast_num b,
        gen_check_flags (E_Literal ast_num (Boolean_Literal b)) nil
    | GCF_Name: forall n flags ast_num,
        gen_name_check_flags n flags ->        (* ########## *)
        gen_check_flags (E_Name ast_num n) nil (* ########## *)
    | GCF_Binary_Operation_Plus: forall ast_num e1 e2,
        gen_check_flags (E_Binary_Operation ast_num Plus e1 e2) (Do_Overflow_Check :: nil)
    | GCF_Binary_Operation_Minus: forall ast_num e1 e2,
        gen_check_flags (E_Binary_Operation ast_num Minus e1 e2) (Do_Overflow_Check :: nil)
    | GCF_Binary_Operation_Multiply: forall ast_num e1 e2,
        gen_check_flags (E_Binary_Operation ast_num Multiply e1 e2) (Do_Overflow_Check :: nil)
    | GCF_Binary_Operation_Div: forall ast_num e1 e2,
        gen_check_flags (E_Binary_Operation ast_num Divide e1 e2) (Do_Division_Check :: Do_Overflow_Check :: nil)
    | GCF_Binary_Operation_Others: forall ast_num op e1 e2,
        op <> Plus ->
        op <> Minus ->
        op <> Multiply ->
        op <> Divide ->
        gen_check_flags (E_Binary_Operation ast_num op e1 e2) nil
    | GCF_Unary_Operation_Minus: forall ast_num e,
        gen_check_flags (E_Unary_Operation ast_num Unary_Minus e) (Do_Overflow_Check :: nil)
    | GCF_Unary_Operation_Others: forall ast_num op e,
        op <> Unary_Minus ->
        gen_check_flags (E_Unary_Operation ast_num op e) nil

with gen_name_check_flags: name -> check_flags -> Prop :=
    | GNCF_Identifier: forall ast_num x,
        gen_name_check_flags (E_Identifier ast_num x) nil
    | GNCF_Indexed_Component: forall ast_num x_ast_num x e,
        gen_name_check_flags (E_Indexed_Component ast_num x_ast_num x e) (Do_Index_Check :: nil)
    | GNCF_Selected_Component: forall ast_num x_ast_num x f,
        gen_name_check_flags (E_Selected_Component ast_num x_ast_num x f) nil.







(******************************************************************

(** ** Functional semantics *)

(** Function for run-time checks generation according to checking rules *)

Function f_check_flags (e: expression): run_time_check_set :=
    match e with
    | E_Literal ast_num n => nil
    | E_Identifier ast_num x => nil
    | E_Binary_Operation ast_num op e1 e2 => 
        match op with
        | Plus => (Do_Overflow_Check :: nil)
        | Minus => (Do_Overflow_Check :: nil)
        | Multiply => (Do_Overflow_Check :: nil)
        | Divide => (Do_Division_Check :: Do_Overflow_Check :: nil)
        | _ => nil
        end
    | E_Unary_Operation ast_num op e => nil
    end.

Function f_do_check (op: binary_operator) (v1: value) (v2: value): option bool :=
    match op with
    | Plus => (* overflow check *)
        match v1, v2 with
        | Int v1', Int v2' => Some ((Zge_bool (v1' + v2') min_signed) && (Zle_bool (v1' + v2') max_signed))
        | _, _ => None
        end
    | Minus => (* overflow check *)
        match v1, v2 with
        | Int v1', Int v2' => Some ((Zge_bool (v1' - v2') min_signed) && (Zle_bool (v1' - v2') max_signed))
        | _, _ => None
        end
    | Multiply => (* overflow check *)
        match v1, v2 with
        | Int v1', Int v2' => Some ((Zge_bool (v1' * v2') min_signed) && (Zle_bool (v1' * v2') max_signed))
        | _, _ => None
        end
    | Divide => (* both division by zero check and overflow check *)
        match v1, v2 with
        | Int v1', Int v2' => 
            Some ((negb (Zeq_bool v2' 0)) && ((Zge_bool (Z.quot v1' v2') min_signed) && (Zle_bool (Z.quot v1' v2') max_signed)))
        | _, _ => None
        end
    | _ => Some true
    end.

(** perform the flagged checks on operators, but at the same time we
    have to ensure that the flagged checks on operators are correct,
    for exmpale, only do Do_Division_Check on Divide make sense, so 
    Do_Division_Check on other operators should return None;
*)
Function f_do_flagged_check (rtc: run_time_checks) (op: binary_operator) (v1: value) (v2: value): option bool :=
    match rtc, op with
    | Do_Overflow_Check, Plus => 
        match v1, v2 with
        | Int v1', Int v2' => Some ((Zge_bool (v1' + v2') min_signed) && (Zle_bool (v1' + v2') max_signed))
        | _, _ => None
        end
    | Do_Overflow_Check, Minus => 
        match v1, v2 with
        | Int v1', Int v2' => Some ((Zge_bool (v1' - v2') min_signed) && (Zle_bool (v1' - v2') max_signed))
        | _, _ => None
        end
    | Do_Overflow_Check, Multiply => 
        match v1, v2 with
        | Int v1', Int v2' => Some ((Zge_bool (v1' * v2') min_signed) && (Zle_bool (v1' * v2') max_signed))
        | _, _ => None
        end
    | Do_Overflow_Check, Divide => 
        match v1, v2 with
        | Int v1', Int v2' => Some ((Zge_bool (Z.quot v1' v2') min_signed) && (Zle_bool (Z.quot v1' v2') max_signed))
        | _, _ => None
        end
    | Do_Division_Check, Divide => 
        match v1, v2 with
        | Int v1', Int v2' => Some (negb (Zeq_bool v2' 0))
        | _, _ => None
        end
    | _, _ => None
    end.

(** perform a series of different checks on one operation *)
Function f_do_flagged_checks (rtcs: run_time_check_set) (op: binary_operator) (v1: value) (v2: value): option bool :=
    match rtcs with
    | nil => Some true
    | rtc :: rtcs' => 
        match f_do_flagged_check rtc op v1 v2 with
        | Some false => Some false
        | Some true => f_do_flagged_checks rtcs' op v1 v2
        | None => None
        end
    end.


(** ** Bisimulation between relational and functional semantics *)

(** bisimulation proof between f_check_flag and check_flag: 
    - f_check_flag_correct
    - f_check_flag_complete
*)
Lemma f_check_flags_correct: forall e cks,
    f_check_flags e = cks ->
    check_flags e cks.
Proof.
    intros e;
    functional induction (f_check_flags e);
    intros ck h1;
    rewrite <- h1;
     try constructor;
    match goal with
    | |- ?op <> Plus => idtac
    | |- ?op <> Minus => idtac
    | |- ?op <> Multiply => idtac
    | |- ?op <> Divide => idtac
    | _ => destruct n; constructor
    end;
    destruct op; inversion y;
    unfold not; intros hz1; inversion hz1.
Qed.

Lemma f_check_flags_complete: forall e cks,
    check_flags e cks ->
    f_check_flags e = cks.
Proof.
    intros e ck h1.
    induction h1;
    auto.
    destruct op; intuition.
Qed.


(** bisimulation proof between f_do_check and do_check: 
    - f_do_check_correct
    - f_do_check_complete
*)
Lemma f_do_check_correct: forall op v1 v2 b,
    f_do_check op v1 v2 = Some b ->
    do_check op v1 v2 b.
Proof.
    intros op v1 v2;
    functional induction (f_do_check op v1 v2);
    intros b h1;
    inversion h1; subst;
    match goal with 
    | |- do_check Plus ?v1 ?v2 ?v => idtac
    | |- do_check Minus ?v1 ?v2 ?v => idtac
    | |- do_check Multiply ?v1 ?v2 ?v => idtac
    | |- do_check Divide ?v1 ?v2 ?v => idtac
    | _ => destruct op; try inversion y;
           constructor; unfold not; intros hz1;
           inversion hz1
    end; constructor; try (rewrite e1); auto.
Qed.

Lemma f_do_check_complete: forall op v1 v2 b,
    do_check op v1 v2 b ->
    f_do_check op v1 v2 = Some b.
Proof.
    intros op v1 v2 b h1.
    induction h1; simpl;
    try (rewrite H; auto).
    destruct op; intuition.
Qed.

Lemma f_do_flagged_check_correct: forall ck op v1 v2 b,
    f_do_flagged_check ck op v1 v2 = Some b ->
    do_flagged_check ck op v1 v2 b.
Proof.
    intros ck op v1 v2;
    functional induction (f_do_flagged_check ck op v1 v2);
    intros b h1;
    inversion h1; subst;
    constructor; auto.
Qed.

Lemma f_do_flagged_check_complete: forall ck op v1 v2 b,
    do_flagged_check ck op v1 v2 b ->
    f_do_flagged_check ck op v1 v2 = Some b.
Proof.
    intros ck op v1 v2 b h1.
    induction h1; simpl;
    rewrite H; auto.
Qed.

Lemma f_do_flagged_checks_correct: forall cks op v1 v2 b,
    f_do_flagged_checks cks op v1 v2 = Some b ->
    do_flagged_checks cks op v1 v2 b.
Proof.
    intros cks op v1 v2;
    functional induction (f_do_flagged_checks cks op v1 v2);
    intros b h1.
  - inversion h1; subst.
    constructor.
  - inversion h1; subst.
    constructor.
    apply f_do_flagged_check_correct; auto.
  - specialize (IHo _ h1).
    constructor; auto.
    apply f_do_flagged_check_correct; auto.
  - inversion h1.
Qed.

Lemma f_do_flagged_checks_complete: forall cks op v1 v2 b,
    do_flagged_checks cks op v1 v2 b ->
    f_do_flagged_checks cks op v1 v2 = Some b.
Proof.
    intros cks op v1 v2 b h1.
    induction h1; simpl; auto.
  - rewrite (f_do_flagged_check_complete _ _ _ _ _ H).
    auto.
  - rewrite (f_do_flagged_check_complete _ _ _ _ _ H).
    auto.
Qed.

(** * Lemmas about run time checks *)

(** whenever perform the flagged checks on the binary operator, 
    if these flagged checks are produced correctly according to 
    the checking rules, then its result should be the same as the
    result by the reference check semantcis do_check;
*)
Lemma do_complete_checks_correct: forall ast_num op e1 e2 cks v1 v2 b,
    check_flags (E_Binary_Operation ast_num op e1 e2) cks ->
    do_flagged_checks cks op v1 v2 b ->
    do_check op v1 v2 b.
Proof.
    intros ast_num op e1 e2 cks v1 v2 b h1 h2.
    destruct op;
    match goal with
    | h: check_flags (E_Binary_Operation _ Plus ?e1 ?e2) ?cks |- _ => idtac
    | h: check_flags (E_Binary_Operation _ Minus ?e1 ?e2) ?cks |- _ => idtac
    | h: check_flags (E_Binary_Operation _ Multiply ?e1 ?e2) ?cks |- _ => idtac
    | h: check_flags (E_Binary_Operation _ Divide ?e1 ?e2) ?cks |- _ => idtac
    | h: check_flags (E_Binary_Operation _ ?op ?e1 ?e2) ?cks |- _ => 
        inversion h1; subst; inversion h2; subst; constructor; rm_always_true
    end.
  - (* Plus *)
    inversion h1; subst.
    + destruct b.
      * inversion h2; subst.
        inversion H1; subst.
        constructor; auto.
      * inversion h2; subst.
        inversion H4; subst.
        constructor; auto.
        inversion H6.
    + rm_false_hyp.
  - (* Minus *)
    inversion h1; subst.
    + destruct b.
      * inversion h2; subst.
        inversion H1; subst.
        constructor; auto.
      * inversion h2; subst.
        inversion H4; subst.
        constructor; auto.
        inversion H6.
    + rm_false_hyp.
  - (* Multiply *)
    inversion h1; subst.
    + destruct b.
      * inversion h2; subst.
        inversion H1; subst.
        constructor; auto.
      * inversion h2; subst.
        inversion H4; subst.
        constructor; auto.
        inversion H6.
    + rm_false_hyp.
  - (* Divide *)
    inversion h1; subst.
    + destruct b.
      * inversion h2; subst.
        inversion H6; subst.
        inversion H2; subst.
        inversion H1; subst.
        constructor; intuition.
      * inversion h2; subst.
        inversion H4; subst.
        constructor; auto.
        rewrite H; auto.
        inversion H6; subst.
        inversion H5; subst.
        constructor. 
        rewrite H. destruct (Zeq_bool v3 0); auto.
        inversion H8.
    + rm_false_hyp.
Qed.


(** whenever perform the flagged checks on the binary operator, 
    if these flagged checks are produced correctly according to 
    the checking rules, then its result should be the same as the
    result by the reference check semantcis do_check;
*)
Lemma do_complete_checks_correct': forall ast_num op e1 e2 cks v1 v2 b,
    check_flags (E_Binary_Operation ast_num op e1 e2) cks ->
    do_check op v1 v2 b ->
    do_flagged_checks cks op v1 v2 b.
Proof.
    intros ast_num op e1 e2 cks v1 v2 b h1 h2.
    destruct op;
    match goal with
    | h: check_flags (E_Binary_Operation _ Plus ?e1 ?e2) ?cks |- _ => idtac
    | h: check_flags (E_Binary_Operation _ Minus ?e1 ?e2) ?cks |- _ => idtac
    | h: check_flags (E_Binary_Operation _ Multiply ?e1 ?e2) ?cks |- _ => idtac
    | h: check_flags (E_Binary_Operation _ Divide ?e1 ?e2) ?cks |- _ => idtac
    | h: check_flags (E_Binary_Operation _ ?op ?e1 ?e2) ?cks |- _ => 
        inversion h1; subst; inversion h2; subst; constructor
    end.
  - (* Plus *)
    inversion h1; subst.
    + destruct b.
      * inversion h2; subst.
        repeat constructor; auto.
        rm_false_hyp.
      * inversion h2; subst.
        repeat constructor; auto.
    + rm_false_hyp.
  - (* Minus *)
    inversion h1; subst.
    + destruct b.
      * inversion h2; subst.
        repeat constructor; auto.
        rm_false_hyp.
      * inversion h2; subst.
        repeat constructor; auto.
    + rm_false_hyp.
  - (* Multiply *)
    inversion h1; subst.
    + destruct b.
      * inversion h2; subst.
        repeat constructor; auto.
        rm_false_hyp.
      * inversion h2; subst.
        repeat constructor; auto.
    + rm_false_hyp.
  - (* Divide *)
    inversion h1; subst.
    + destruct b.
      * inversion h2; subst.
        repeat constructor;
        destruct (Zeq_bool v3 0); inversion H; auto.
        rm_false_hyp.
      * inversion h2; subst.
        remember (negb (Zeq_bool v3 0)) as x.
        symmetry in Heqx; destruct x; simpl in H.
        apply Do_Checks_True;
        repeat constructor; auto.
        repeat constructor; auto.
    + rm_false_hyp.
Qed.


(** 
    this lemma is used only to prove binop_rule2, which means that
    run time checks on a binary operator with two integer values 
    should always return a value b, which can be either true or false;
*)

Lemma do_check_result_ex: forall op v1 v2,
    exists b : bool, do_check op (Int v1) (Int v2) b.
Proof.
    intros op v1 v2.
    destruct op;   
    try match goal with
    | [ |- exists r : bool, do_check Plus (Int ?v1) (Int ?v2) r ] => idtac
    | [ |- exists r : bool, do_check Minus (Int ?v1) (Int ?v2) r ] => idtac
    | [ |- exists r : bool, do_check Multiply (Int ?v1) (Int ?v2) r ] => idtac
    | [ |- exists r : bool, do_check Divide (Int ?v1) (Int ?v2) r ] => idtac
    | [ |- exists r : bool, do_check ?op (Int ?v1) (Int ?v2) r ] =>
            exists true; constructor; rm_always_true
    end.
    + (* Plus *)
      remember ((Zge_bool (v1 + v2) min_signed) && (Zle_bool (v1 + v2) max_signed)) as b.
      destruct b;
      [exists true | exists false];
      constructor; auto.
    + (* Minus *)
      remember ((Zge_bool (v1 - v2) min_signed) && (Zle_bool (v1 - v2) max_signed)) as b.
      destruct b;
      [exists true | exists false];
      constructor; auto.
    + (* Multiply *)
      remember ((Zge_bool (v1 * v2) min_signed) && (Zle_bool (v1 * v2) max_signed)) as b.
      destruct b;
      [exists true | exists false];
      constructor; auto.
    + (* Divide *)
      destruct v2.
      * exists false; 
        constructor; auto.
      * remember ((Zge_bool (Z.quot v1 (Z.pos p)) min_signed) && (Zle_bool (Z.quot v1 (Z.pos p)) max_signed)) as b.
        destruct b;
        [exists true | exists false];
        constructor; auto.
      * remember ((Zge_bool (Z.quot v1 (Z.neg p)) min_signed) && (Zle_bool (Z.quot v1 (Z.neg p)) max_signed)) as b.
        destruct b;
        [exists true | exists false];
        constructor; auto.
Qed.
******************************************************************)
