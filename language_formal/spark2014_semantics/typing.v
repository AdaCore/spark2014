Require Import environment.

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

(** * Type Check Stack *)

(** ** Type checker for store *)
(** for any valid variable x, it has an in/out mode, type and value 
    (either defined or undefined); as the in/out mode and type are
    invariant since the variable is declared, and they are used only
    at compile time, we keep these invariant information in a symbol 
    table called _symtb_; while the value of a variable will change 
    as the program executes, and it's used in run time evaluation, 
    so we keep this information in a store called _store_;
    
    Type Check Stack means: for any variable x, its stored value in
    store should be consistent with its declared type recorded in
    symbol table symtb;
    
    This section defines the type checker for store in both relational
    and functional logic and prove their bisimulation relation
    - relational one: type_check_store;
    - functional one: f_type_check_store;
    - bisilumation proof between relational and functional one;
*)
Inductive type_check_store: symtb -> store -> Prop :=
    | TC_Empty: type_check_store nil nil
    | TC_Bool: forall tb s x m b,
          type_check_store tb s ->
          type_check_store ((x, (m, Boolean)) :: tb) ((x, (Value (Bool b))) :: s)
    | TC_Int: forall tb s x m v,
          type_check_store tb s ->
          type_check_store ((x, (m, Integer)) :: tb) ((x, (Value (Int v))) :: s)
    | TC_Undefined_Bool: forall tb s x m,
          type_check_store tb s ->
          type_check_store ((x, (m, Boolean)) :: tb) ((x, Undefined) :: s)
    | TC_Undefined_Int: forall tb s x m,
          type_check_store tb s ->
          type_check_store ((x, (m, Integer)) :: tb) ((x, Undefined) :: s).

Function f_type_check_store (tb: symtb) (s: store): bool :=
    match tb, s with
    | nil, nil => true
    | (u :: tb'), (v :: s') => 
        match u, v with
        | (x, (m, Boolean)), (y, (Value (Bool b))) => 
            if beq_nat x y then f_type_check_store tb' s' else false
        | (x, (m, Integer)), (y, (Value (Int v))) => 
            if beq_nat x y then f_type_check_store tb' s' else false
        | (x, (m, Boolean)), (y, Undefined) => 
            if beq_nat x y then f_type_check_store tb' s' else false
        | (x, (m, Integer)), (y, Undefined) => 
            if beq_nat x y then f_type_check_store tb' s' else false
        | _, _ => false
        end
    | _, _ => false
    end.

(** Bisimulation proof between f_type_check_store and type_check_store: 
    - f_type_check_store_correct
    - f_type_check_store_complete
*)
Lemma f_type_check_store_correct: forall tb s,
    f_type_check_store tb s = true ->
        type_check_store tb s.
Proof.
    intros tb s.
    functional induction (f_type_check_store tb s);
    intros h1;
    try match goal with
    | h: false = true |- _ => inversion h
    | h: beq_nat ?x ?y = true |- _ => rewrite (beq_nat_true _ _ e3)
    end; constructor; auto.
Qed.

Lemma f_type_check_store_complete: forall tb s,
    type_check_store tb s ->
        f_type_check_store tb s = true.
Proof.
    intros tb s h1.
    induction h1;
    simpl;
    repeat match goal with
    | |- context[beq_nat ?x ?x] => rewrite <- (beq_nat_refl x)
    | h: f_type_check_store ?tb ?s = true |- _ => rewrite h
    end; auto.
Qed.

(** ** Some lemmas *)
(** typed_value means: for any variable x in a type checked store,
    it should has some type t that can be found in the symbol table;
*)
Lemma typed_value: forall tb s x v,
    type_check_store tb s ->
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

(** typed_value' means: for any type checked store s with respect to 
    the symbol table tb, if tb includes a variable x of type t, then 
    x should also reside in store s, and if x has a defined value v,
    then v should have the type of t;
*)
Lemma typed_value': forall tb s x m t,
    type_check_store tb s ->
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
