Require Export values.

(** for any valid variable x, it has an in/out mode, type and value 
    (either defined or undefined); as the in/out mode and type are
    invariant since the variable is declared, and they are used only
    at compile time, we keep these invariant information in a symbol 
    table called _symtb_; while the value of a variable will change 
    as the program executes, and it's used in run time evaluation, 
    so we keep this information in a stack called _stack_;
*)

(** * Stack *)

(** ** Stack as a list *)
(** it's a map from a variable, represented with natural number,
    to its value;
*)
Definition stack : Type := list (idnum * val).

(** ** Stack operations *)
(** check whether variable x has already been declared *)
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
Lemma fetch_in: forall x s v, 
    fetch x s = Some v -> List.In (x, Value v) s.
Proof.
    intros x s.
    functional induction (fetch x s);
    intros v1 H;
    try match goal with
    | h: None = Some ?v |- _ => inversion h
    | h: Some ?v1 = Some ?v2 |- _ => inversion h; subst
    end; simpl.
  - apply beq_nat_true_iff in e0; subst.
    left;auto.
  - right.
    apply IHo.
    assumption.
Qed.

Lemma update_in: forall s x v' s', 
    update s x v' = Some s' -> (exists v, List.In (x, v) s).
Proof.
    intros s x v'.
    functional induction (update s x v');
    intros s1 h1;
    try match goal with
    | h: None = Some ?s |- _ => inversion h
    | h: beq_nat _ _ = true |- _  => rewrite beq_nat_true_iff in h; subst
    end.
  - exists v'. 
    simpl.
    left; auto.
  - specialize (IHo s'' e1).
    inversion IHo.
    exists x0. simpl. 
    right; assumption.
Qed.
    
Lemma in_update: forall s x v' y v s',
                   update s x v' = Some s' ->
                   List.In (y, v) s'
                   -> ((y=x /\ v=v') \/ List.In (y,v) s).
Proof.
    intros s x v'.
    functional induction (update s x v'); simpl; intros y0 v0 s0 h h'; subst;
    (inversion h; clear h); subst.
    apply beq_nat_true_iff in e0; subst.
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

(** * Symbol Table *)

(** ** Symbol table as a list *)
(** it's a map from a variable, represented as natural number,
    to a pair of in/out mode and it's declared type;
*)
Definition symtb: Type := list (idnum * (mode * type)).

(** ** Symbol table operations *)
Fixpoint lookup (x : idnum) (tb: symtb) := 
   match tb with 
   | (y, (m,t)) :: tb' => if (beq_nat x y) then Some (m, t) else lookup x tb' 
   | nil => None
   end.

(** * Program State *)
(** Statement evaluation returns one of the following results:
    - normal state;
    - run time errors, which is caught by run time checks,
      for example, overflow check and division by zero check;
    - unterminated state because of the loop;
    - abnormal state, which includes compile time errors
      (for example, type checks failure and undefined variables), 
      bounded errors and erroneous execution. In the future, 
      if it's necessary, we would refine the abnormal state into 
      these more precise categories (1.1.5);
*)

Inductive state: Type :=
    | S_Normal: stack -> state
    | S_Run_Time_Error: state
    | S_Unterminated: state
    | S_Abnormal: state.

(** * Type Check Stack *)

(** ** Type checker for stack *)
(** for any valid variable x, it has an in/out mode, type and value 
    (either defined or undefined); as the in/out mode and type are
    invariant since the variable is declared, and they are used only
    at compile time, we keep these invariant information in a symbol 
    table called _symtb_; while the value of a variable will change 
    as the program executes, and it's used in run time evaluation, 
    so we keep this information in a stack called _stack_;
    
    Type Check Stack means: for any variable x, its stored value in
    stack should be consistent with its declared type recorded in
    symbol table symtb;
    
    This section defines the type checker for stack in both relational
    and functional logic and prove their bisimulation relation
    - relational one: type_check_stack;
    - functional one: f_type_check_stack;
    - bisilumation proof between relational and functional one;
*)
Inductive type_check_stack: symtb -> stack -> Prop :=
    | TC_Empty: type_check_stack nil nil
    | TC_Bool: forall tb s x m b,
          type_check_stack tb s ->
          type_check_stack ((x, (m, Boolean)) :: tb) ((x, (Value (Bool b))) :: s)
    | TC_Int: forall tb s x m v,
          type_check_stack tb s ->
          type_check_stack ((x, (m, Integer)) :: tb) ((x, (Value (Int v))) :: s)
    | TC_Undefined_Bool: forall tb s x m,
          type_check_stack tb s ->
          type_check_stack ((x, (m, Boolean)) :: tb) ((x, Undefined) :: s)
    | TC_Undefined_Int: forall tb s x m,
          type_check_stack tb s ->
          type_check_stack ((x, (m, Integer)) :: tb) ((x, Undefined) :: s).

Function f_type_check_stack (tb: symtb) (s: stack): bool :=
    match tb, s with
    | nil, nil => true
    | (u :: tb'), (v :: s') => 
        match u, v with
        | (x, (m, Boolean)), (y, (Value (Bool b))) => 
            if beq_nat x y then f_type_check_stack tb' s' else false
        | (x, (m, Integer)), (y, (Value (Int v))) => 
            if beq_nat x y then f_type_check_stack tb' s' else false
        | (x, (m, Boolean)), (y, Undefined) => 
            if beq_nat x y then f_type_check_stack tb' s' else false
        | (x, (m, Integer)), (y, Undefined) => 
            if beq_nat x y then f_type_check_stack tb' s' else false
        | _, _ => false
        end
    | _, _ => false
    end.

(** Bisimulation proof between f_type_check_stack and type_check_stack: 
    - f_type_check_stack_correct
    - f_type_check_stack_complete
*)
Lemma f_type_check_stack_correct: forall tb s,
    f_type_check_stack tb s = true ->
        type_check_stack tb s.
Proof.
    intros tb s.
    functional induction (f_type_check_stack tb s);
    intros h1;
    try match goal with
    | h: false = true |- _ => inversion h
    | h: beq_nat ?x ?y = true |- _ => rewrite (beq_nat_true _ _ e3)
    end; constructor; auto.
Qed.

Lemma f_type_check_stack_complete: forall tb s,
    type_check_stack tb s ->
        f_type_check_stack tb s = true.
Proof.
    intros tb s h1.
    induction h1;
    simpl;
    repeat match goal with
    | |- context[beq_nat ?x ?x] => rewrite <- (beq_nat_refl x)
    | h: f_type_check_stack ?tb ?s = true |- _ => rewrite h
    end; auto.
Qed.

(** ** Some lemmas *)
(** typed_value means: for any variable x in a type checked stack,
    it should has some type t that can be found in the symbol table;
*)
Lemma typed_value: forall tb s x v,
    type_check_stack tb s ->
    fetch x s = Some v ->
    (exists t, value_of_type v t /\ ( exists m, lookup x tb = Some (m, t))).
Proof.
    intros tb s x v h1 h2.
    destruct v.
  - exists Integer.
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
  - exists Boolean.
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

Ltac rm_ex :=
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
      rm_ex; auto
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
      rm_ex; auto
    ].

(** typed_value' means: for any type checked stack s with respect to 
    the symbol table tb, if tb includes a variable x of type t, then 
    x should also reside in stack s, and if x has a defined value v,
    then v should have the type of t;
*)
Lemma typed_value': forall tb s x m t,
    type_check_stack tb s ->
    lookup x tb = Some (m, t) -> 
    reside x s = true /\ 
    (forall v, (Some v = fetch x s) -> value_of_type v t).
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
