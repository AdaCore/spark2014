Require Export values.

(** * Stack *)

(** ** Stack as a list *)
Definition stack : Type := list (idnum * val).

(** ** Stack operations *)
Function reside (x : idnum) (s : stack) := 
    match s with 
    | (y, v) :: s' =>
      if beq_nat x y then
        true
      else 
        reside x s' 
    | nil => false
    end.

(** fetch the value of x that has already been initialized in stack *)
Function fetch (x : idnum) (s : stack): option value := 
    match s with 
    | (y, v) :: s' =>
      if beq_nat x y then
        match v with
        | Value v => Some v
        | Vundef => None
        end
      else fetch x s' 
    | nil => None
    end.

(** update the latest binding for x *)
Function update (s: stack) (x : idnum) (v: val): option stack := 
    match s with 
    | (y, v') :: s' => 
      if beq_nat x y then 
        Some ((y,v)::s') 
      else 
        match update s' x v with
        | Some s'' => Some ((y,v')::s'')
        | None => None
        end
   | nil => None
   end.

(** ** Lemmas about stack operations *)
Lemma fetch_in: forall x s v, fetch x s = Some v -> List.In (x, Value v) s.
Proof.
    intros x s.
    functional induction (fetch x s).
  - intros v H.
    inversion H; clear H; subst.
    rewrite beq_nat_true_iff in e0.
    rewrite e0.
    simpl.
    left;auto.
  - intros v H.
    inversion H. 
  - intros v0 H.
    simpl.
    right.
    apply IHo.
    assumption.
  - intros v H.
    inversion H.
Qed.

Lemma update_in: forall s x v' s', update s x v' = Some s' -> (exists v, List.In (x, v) s).
Proof.
    intros s x v'.
    functional induction (update s x v');
    try match goal with
    | [h: beq_nat _ _ = true |- _ ] => rewrite beq_nat_true_iff in h; subst
    end; intros s1 h1.
  - exists v'. 
    simpl. left; auto.
  - specialize (IHo s'' e1).
    inversion IHo.
    exists x0. simpl. 
    right; assumption.
  - inversion h1.
  - inversion h1.
Qed.
    
Lemma in_update: forall s x v' y v s',
                   update s x v' = Some s' ->
                   List.In (y, v) s'
                   -> ((y=x /\ v=v') \/ List.In (y,v) s).
Proof.
    intros s x v'.
    functional induction (update s x v'); simpl; intros y0 v0 s0 h h'; subst;
    (inversion h; clear h); subst.
    rewrite beq_nat_true_iff in e0; subst.
  - destruct h'.
    + left. inversion H; auto.
    + right. right; assumption.
  - specialize (IHo y0 v0 s'' e1).
    destruct h'.
    + right. left. assumption.
    + specialize (IHo H). 
       destruct IHo as [h | h'].
       *  left; assumption.
       * right. right; assumption.
Qed.

(*
Lemma update_fetch_new: forall v v0 s x  s',
    v = Value v0 ->
    update s x v = Some s' ->
    fetch x s' = Some v0.
Proof.
    intros v v0 s x.
    functional induction (update s x v);
    intros s'0 h1 h2; subst.
  - inversion h2; subst.
    unfold fetch.
    rewrite e0.
    auto.
  - inversion h2; subst.
    apply IHo.
    auto. admit.

Qed.

Lemma update_fetch_old: forall s x v s' y,
    update s x (Value v) = Some s' ->
    y <> x ->
    fetch y s' = fetch y s.
Proof.

Qed.
*)

(** * Symbol Table *)

(** ** Symbol table as a list *)
Definition symtb: Type := list (idnum * (mode * typ)).

(** ** Symbol table operations *)
Fixpoint lookup (x : idnum) (tb: symtb) := 
   match tb with 
   | (y, (m,t)) :: tb' => if (beq_nat x y) then Some (m, t) else lookup x tb' 
   | nil => None
   end.

(** * Program State *)
(** 
    possible state after running a command:
    - a normal resultant stack
    - an exception (such as overflow, division by zero and so on)
    - an unterminated state
    - an abnormal (unexpected) state
*)
Inductive state: Type :=
    | SNormal: stack -> state
    | SException: state
    | SUnterminated: state
    | SAbnormal: state.

(** * Type Check Stack *)

(** ** Type checker *)
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

(** ** Some lemmas *)
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

Ltac rm_exists1 :=
    repeat match goal with
    | [ h: exists _, _ |- _ ] => inversion h; clear h
    | [ h: _ /\ _  |- _ ] => inversion h; clear h
    end.

Ltac tv_l1 f1 f2 h1 h2 x x0 := 
    unfold f1 in h1;
    unfold f2;
    destruct (beq_nat x x0);
    [ auto |
      fold f1 in h1;
      fold f2;
      specialize (h2 h1);
      rm_exists1; auto
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
      rm_exists1; auto
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


 