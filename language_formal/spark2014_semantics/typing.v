Require Import LibTactics.
Require Import semantics.
Require Import Setoid.
Require Import Morphisms.
Require Import values.
Require Import environment.

(** * Symbol Table *)

Module Entry_type <: Entry.

Inductive type_stored : Type :=
| BasicType: type -> type_stored
| ProcType: list parameter_specification -> type_stored.

Definition T:= (mode*type_stored)%type.

End Entry_type.

Module Import TSTACK := ENV(Entry_type).
Import Entry_type.


Inductive type_of_value: val -> type_stored -> Prop :=
| TV_Int: forall n, type_of_value (Value (Int n)) (BasicType Integer)
| TV_Bool: forall b, type_of_value (Value (Bool b)) (BasicType Boolean)
| TV_Proc: forall pb, type_of_value (Procedure pb) (ProcType (procedure_parameter_profile pb)).


Scheme Equality for mode.

Lemma beq_mode_iff1 x: mode_beq x x = true.
Proof.
  destruct x;simpl;auto.
Qed.

Lemma beq_mode_iff2 x y: x<>y -> mode_beq x y = false.
Proof.
  destruct x;destruct y;simpl;auto;intros;try contradiction.
  - destruct H. reflexivity.
  - destruct H. reflexivity.
  - destruct H. reflexivity.
Qed.


Lemma beq_mode_true_iff : forall x y, mode_beq x y = true <-> x = y.
Proof.
  intros x y.
  destruct (mode_eq_dec x y);subst.
  - split;intro.
    + reflexivity.
    + apply beq_mode_iff1.
  - split;intro.
    + apply beq_mode_iff2 in n.
      rewrite H in n; discriminate.
    + contradiction.
Qed.



Definition beq_parameter_specification (x y:parameter_specification) : bool :=
  (beq_nat x.(parameter_subtype_mark) y.(parameter_subtype_mark))
    &&
    (mode_beq x.(parameter_mode) y.(parameter_mode)).

Definition eq_parameter_specification (x y:parameter_specification) : Prop :=
  (x.(parameter_subtype_mark) = y.(parameter_subtype_mark))
    /\ (x.(parameter_mode) = y.(parameter_mode)).

Lemma eq_parameter_specification_correct: forall x y,
  eq_parameter_specification x y  <-> beq_parameter_specification x y = true.
Proof.
  intros x y.
  unfold eq_parameter_specification,beq_parameter_specification;simpl.
  rewrite andb_true_iff.
  rewrite beq_nat_true_iff.
  rewrite beq_mode_true_iff.
  reflexivity.
Qed.

Inductive eq_parameter_specification_list:
  list parameter_specification -> list parameter_specification -> Prop :=
| Eq_paramlis_nil: eq_parameter_specification_list nil nil
| Eq_paramlis_cons: forall x y a b,
    eq_parameter_specification x y ->
    eq_parameter_specification_list a b ->
    eq_parameter_specification_list (x::a) (y::b).

Function beq_parameter_specification_list (x y:list parameter_specification) {struct x}
: bool :=
  match x,y with
    | nil,nil => true
    | a::x' , b ::y' =>
      beq_parameter_specification a b &&
      beq_parameter_specification_list x' y'
| _,_ => false
  end.

Lemma beq_parameter_specification_list_iff:
  forall l1 l2,
    eq_parameter_specification_list l1 l2 <->
    beq_parameter_specification_list l1 l2 = true.
Proof.
  intros l1 l2.
  split.
  - intros h.
    induction h;simpl;auto.
    rewrite eq_parameter_specification_correct in H.
    rewrite H.
    rewrite IHh.
    reflexivity.
  - revert l2.
    induction l1;intros l2 h;simpl.
    + functional inversion h;subst.
      constructor 1.
    + functional inversion h;subst.
      constructor 2.
      * rewrite andb_true_iff in H1.
        destruct H1.
        rewrite eq_parameter_specification_correct.
        assumption.
      * apply IHl1.
        rewrite andb_true_iff in H1.
        destruct H1.
        assumption.
Qed.


Inductive compatible_type_of_value: val -> type_stored -> Prop :=
| CTV_Int: forall n, compatible_type_of_value (Value (Int n)) (BasicType Integer)
| CTV_Bool: forall b, compatible_type_of_value (Value (Bool b)) (BasicType Boolean)
| CTV_Undef: forall t, compatible_type_of_value (Undefined) (BasicType t)
| CTV_Proc: forall pb prf,
              eq_parameter_specification_list prf (procedure_parameter_profile pb) ->
              compatible_type_of_value (Procedure pb) (ProcType prf).


Lemma eq_parameter_specification_refl : reflexive _ eq_parameter_specification.
Proof.
  hnf.
  intros x.
  hnf.
  split;reflexivity.
Qed.

Lemma eq_parameter_specification_sym : symmetric _ eq_parameter_specification.
Proof.
  hnf.
  intros x y.
  unfold eq_parameter_specification.
  intros h.
  intuition.
Qed.

Lemma eq_parameter_specification_trans : transitive _ eq_parameter_specification.
Proof.
  hnf.
  intros x y z.
  unfold eq_parameter_specification.
  intros h1 h2.
  intuition.
  - rewrite H.
    rewrite H1.
    reflexivity.
  - rewrite H0.
    rewrite H2.
    reflexivity.
Qed.

Add Parametric Relation: parameter_specification eq_parameter_specification
    reflexivity proved by eq_parameter_specification_refl
    symmetry proved by eq_parameter_specification_sym
    transitivity proved by eq_parameter_specification_trans
      as eq_parameter_specification_equiv_rel.

Lemma eq_parameter_specification_list_refl : reflexive _ eq_parameter_specification_list.
Proof.
  hnf.
  induction x.
  - constructor.
  - constructor.
    + reflexivity.
    + assumption.
Qed.

Lemma eq_parameter_specification_list_sym : symmetric _ eq_parameter_specification_list.
Proof.
  hnf.
  intros x y H.
  induction H.
  - constructor.
  - constructor.
    + symmetry.
      assumption.
    + assumption.
Qed.

Lemma eq_parameter_specification_list_trans : transitive _ eq_parameter_specification_list.
Proof.
  hnf.
  intros x y z h.
  revert z.
  induction h;intros z h'.
  - inversion h'.
    subst.
    constructor.
  - inversion h';subst.
    constructor.
    + transitivity y;auto.
    + apply IHh.
      assumption.
Qed.

Add Parametric Relation: (list parameter_specification) eq_parameter_specification_list
    reflexivity proved by eq_parameter_specification_list_refl
    symmetry proved by eq_parameter_specification_list_sym
    transitivity proved by eq_parameter_specification_list_trans
      as eq_parameter_specification_list_equiv_rel.


Inductive type_stored_eq : type_stored -> type_stored -> Prop :=
| TS_eq1: forall x y,
            eq_parameter_specification_list x y
            -> type_stored_eq (ProcType x) (ProcType y)
| TS_eq2: forall x y,
            x = y
            -> type_stored_eq (BasicType x) (BasicType y).


Lemma type_stored_eq_refl : reflexive _ type_stored_eq.
Proof.
  hnf.
  destruct x.
  - constructor.
    reflexivity.
  - constructor.
    reflexivity.
Qed.

Lemma type_stored_eq_sym : symmetric _ type_stored_eq.
Proof.
  hnf.
  intros x y H.
  destruct H.
  - constructor.
    symmetry.
    assumption.
  - constructor.
    symmetry.
    assumption.
Qed.

Lemma type_stored_eq_trans : transitive _ type_stored_eq.
Proof.
  hnf.
  intros x y z h.
  destruct h;intros h'.
  - inversion h'.
    subst.
    constructor.
    transitivity y;auto.
  - inversion h';subst.
    assumption.
Qed.

Add Parametric Relation: type_stored type_stored_eq
    reflexivity proved by type_stored_eq_refl
    symmetry proved by type_stored_eq_sym
    transitivity proved by type_stored_eq_trans
      as type_stored_eq_equiv_rel.



Add Parametric Morphism: 
  compatible_type_of_value
    with signature eq ==> type_stored_eq ==> iff
    as compatible_type_of_value_morph.
Proof.
  intros y x y0 H.
  destruct H.
  - split.
    + intros h.
      inversion h.
      subst.
      constructor.
      transitivity x.
      * symmetry.
        assumption.
      * assumption.
    + intros h.
      inv h.
      constructor.
      transitivity y0;auto.
  - subst.
    reflexivity.
Qed.


(** ** Symbol table as a list *)
(** it's a map from a variable, represented as natural number,
    to a pair of in/out mode and it's declared type;
*)

Definition symtb: Type :=  TSTACK.stack.

(** * Type Check Store *)



(** ** Type checker for store *)
(** A store is a frame of a procedure.
    for any valid variable x, it has an in/out mode, type and value 
    (either defined or undefined); as the in/out mode and type are
    invariant since the variable is declared, and they are used only
    at compile time, we keep these invariant information in a symbol 
    table called _symtb_; while the value of a variable will change 
    as the program executes, and it's used in run time evaluation, 
    so we keep this information in a store called _store_;
    
    Type Check Store means: for any variable x, its stored value in
    store should be consistent with its declared type recorded in
    symbol table symtb;
    
    This section defines the type checker for store in both relational
    and functional logic and prove their bisimulation relation
    - relational one: type_check_store;
    - functional one: f_type_check_store;
    - bisilumation proof between relational and functional one;
*)
Inductive type_check_store: TSTACK.store -> STACK.store -> Prop :=
    | TCS_Empty: type_check_store nil nil
    | TCS_Bool: forall tb s x m b,
          type_check_store tb s ->
          type_check_store ((x, (m, BasicType Boolean)) :: tb) ((x, (Value (Bool b))) :: s)
    | TCS_Int: forall tb s x m v,
          type_check_store tb s ->
          type_check_store ((x, (m, BasicType Integer)) :: tb) ((x, (Value (Int v))) :: s)
    | TCS_Undefined_Bool: forall tb s x m,
          type_check_store tb s ->
          type_check_store ((x, (m, BasicType Boolean)) :: tb) ((x, Undefined) :: s)
    | TCS_Undefined_Int: forall tb s x m,
          type_check_store tb s ->
          type_check_store ((x, (m, BasicType Integer)) :: tb) ((x, Undefined) :: s)
    | TCS_Procedure: forall tb s x m proctype pb ,
        eq_parameter_specification_list proctype (procedure_parameter_profile pb) ->
        type_check_store tb s ->
        type_check_store ((x, (m, ProcType proctype)) :: tb) ((x, Procedure pb) :: s).




Function f_type_check_store (tb: TSTACK.store) (s: STACK.store): bool :=
    match tb, s with
    | nil, nil => true
    | ((x,(m,BasicType Integer)) :: tb'), ((y, (Value (Int _))) :: s')
    | ((x,(m,BasicType Boolean)) :: tb'), ((y, (Value (Bool _))) :: s') =>
      if beq_nat x y then f_type_check_store tb' s' else false
    | ((x,(m,BasicType _)) :: tb'), ((y, Undefined) :: s') => 
      if beq_nat x y then f_type_check_store tb' s' else false
    | ((x,(m,ProcType proct)) :: tb'), ((y, Procedure pb) :: s') => 
      if beq_parameter_specification_list proct (procedure_parameter_profile pb)
      then
        if beq_nat x y then f_type_check_store tb' s' else false
      else false
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
      try rewrite beq_nat_true_iff in *;subst;
      try now (intros h1;
               try match goal with
                     | h: false = true |- _ => inversion h
                     | h: beq_nat ?x ?y = true |- _ => rewrite (beq_nat_true _ _ e3)
                   end; constructor; auto).

    - intros h1.
      destruct _x; constructor;auto.
    - intros h1.
      constructor.
      + apply beq_parameter_specification_list_iff.
        assumption.
      + auto.
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
    apply beq_parameter_specification_list_iff in H.
    rewrite H.
    reflexivity.
Qed.


(* TODO: This is an attempt at giving good names automatically to
   hypothesis. This is not perfect but should make scripts more
   robust. This is far from perfect however:

1) I did not manage to make a real tactical, because idify must be
   undone on hypothesis used by the tactic itself.
2) rename_norm is not idempotent, which prevents from calling it
   everywhere.
 *)

Ltac rename_and_idify H hname :=
  let th := type of H in
  rename H into hname;
  change (id th) in hname;
  rename_norm;
  change th in hname

with rename_norm :=
  match reverse goal with
    | H: (type_check_store _ _) |- _ =>
      let s := fresh "htype_check_store" in
      rename_and_idify H s
    | H: (beq_nat _ _ = _) |- _ =>
      let s := fresh "hbeq" in
      rename_and_idify H s
    | H: (compatible_type_of_value _ _) |- _ =>
      let s := fresh "hcompat_t_v" in
      rename_and_idify H s
    | H: STACK.fetch _ _ = _ |- _ =>
      let s := fresh "heqfetch" in
      rename_and_idify H s
    | H: STACK.fetchG _ _ = _ |- _ =>
      let s := fresh "heqfetchG" in
      rename_and_idify H s
    | H: fetchG _ _ = _ |- _ =>
      let s := fresh "heqTfetchG" in
      rename_and_idify H s
    | H: fetch _ _ = _ |- _ =>
      let s := fresh "heqTfetch" in
      rename_and_idify H s
    | H: ?f _ _ = _ |- _ =>
      let s := fresh "heq" f in
      rename_and_idify H s
    | _ => idtac
  end.






(** ** Some lemmas *)
(** For any variable x in a type checked store, it should has some
    type t that is compatible with what is in the symbol table;.
*)
Lemma type_check_store_spec1:
  forall tb s x v,
    type_check_store tb s ->
    STACK.fetch x s = Some v ->
    exists t,
      (compatible_type_of_value v t
       /\ exists m, TSTACK.fetch x tb = Some (m, t)).
Proof.
  intros tb s x v h1 h2.
  induction h1;functional inversion h2;subst;rename_norm;simpl;try rewrite hbeq;eauto.
  - exists (BasicType Boolean);split;try constructor;eauto.
  - exists (BasicType Integer);split;try constructor;eauto.
  - exists (BasicType Boolean);split;try constructor;eauto.
  - exists (BasicType Integer);split;try constructor;eauto.
  - exists (ProcType proctype);split;try constructor;eauto.
Qed.


(** typed_value' means: for any type checked store s with respect to 
    the symbol table tb, if tb includes a variable x of type t, then 
    x should also reside in store s, and if x has a defined value v,
    then v should have the type of t;
*)
Lemma type_check_store_spec2: forall tb s x m t,
    type_check_store tb s ->
    fetch x tb = Some (m, t) -> 
    exists v, (STACK.fetch x s = Some v /\ compatible_type_of_value v t).
Proof.
    intros tb s x m t h1 h2.
    induction h1;functional inversion h2;subst;rename_norm
    ; simpl;try rewrite hbeq;eauto.
    - exists (Value (Bool b));split;auto;constructor.
    - exists (Value (Int v));split;auto;constructor.
    - exists Undefined;split;auto;constructor.
    - exists Undefined;split;auto;constructor.
    - exists (Procedure pb);split;auto;constructor.
      assumption.
Qed.


Lemma type_check_store_spec2_none: forall tb s x,
    type_check_store tb s ->
    fetch x tb = None -> 
    STACK.fetch x s = None.
Proof.
  intros tb s x h1 h2.
  induction h1;functional inversion h2;subst;rename_norm
    ; simpl;try rewrite hbeq;auto; split;auto;intros v' h;inv h.
Qed.

Lemma type_check_store_spec1_none:
  forall tb s x,
    type_check_store tb s ->
    STACK.fetch x s = None ->
    TSTACK.fetch x tb = None.
Proof.
  intros tb s x h1 h2.
  induction h1;functional inversion h2;subst;rename_norm;simpl;try rewrite hbeq;auto.
Qed.


(** * Equality on stacks *)

(** ** Type checker for stack *)
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
Inductive type_check_stack: TSTACK.stack -> STACK.stack -> Prop :=
    | TCST_nil: type_check_stack nil nil
    | TCST_cons: forall sto1 sto2 st1 st2,
                   type_check_store sto1 sto2 ->
                   type_check_stack st1 st2 ->
                   type_check_stack (sto1::st1) (sto2::st2).


Function f_type_check_stack (tb: TSTACK.stack) (s: STACK.stack): bool :=
    match tb, s with
    | nil, nil => true
    | (sto1::st1), (sto2::st2) =>
      if f_type_check_store sto1 sto2 then
        f_type_check_stack st1 st2
      else false
    | _ , _  => false
    end.

(** Bisimulation proof between f_type_check_store and type_check_store: 
    - f_type_check_store_correct
    - f_type_check_store_complete
*)
Lemma f_type_check_stack_correct: forall tb s,
    f_type_check_stack tb s = true ->
        type_check_stack tb s.
Proof.
    intros tb s.
    functional induction (f_type_check_stack tb s);intros; try discriminate;rename_norm.
    - constructor.
    - constructor;auto.
      apply f_type_check_store_correct.
      assumption.
Qed.

Lemma f_type_check_stack_complete: forall tb s,
    type_check_stack tb s ->
        f_type_check_stack tb s = true.
Proof.
    intros tb s h1.
    induction h1;simpl;auto.
    rewrite f_type_check_store_complete;auto.
Qed.


Lemma type_check_stack_spec1:
  forall tb s x v,
    type_check_stack tb s ->
    STACK.fetchG x s = Some v ->
    exists t,
      (compatible_type_of_value v t
       /\ exists m, TSTACK.fetchG x tb = Some (m, t)).
Proof.
  intros tb s x v h1.
  revert x v.
  induction h1;intros x v h2.
  - functional inversion h2.
  - functional inversion h2;subst;rename_norm.
    + apply (type_check_store_spec1 sto1 sto2 x v) in htype_check_store.
      * decomp htype_check_store;rename_norm;rename_norm.
        exists x0.
        split;auto.
        exists x1.
        simpl.
        rewrite heqTfetch.
        reflexivity.
      * assumption.      
    + eapply type_check_store_spec1_none with sto1 sto2 x in htype_check_store;auto.
      specialize (IHh1 _ _ heqfetchG0).
      decomp IHh1.
      exists x0.
      split;auto.
      exists x1.
      simpl.
      rewrite heqTfetchG.
      rewrite htype_check_store.
      reflexivity.
Qed.

(** typed_value' means: for any type checked store s with respect to 
    the symbol table tb, if tb includes a variable x of type t, then 
    x should also reside in store s, and if x has a defined value v,
    then v should have the type of t;
*)
Lemma type_check_stack_spec2: forall tb s x m t,
    type_check_stack tb s ->
    fetchG x tb = Some (m, t) -> 
    (exists v,  STACK.fetchG x s = Some v /\ compatible_type_of_value v t).
Proof.
    intros tb s x m t h1 h2.
    induction h1;functional inversion h2;subst;rename_norm.
    - functional inversion heqTfetchG;subst; clear heqTfetchG;rename_norm;rename_norm.
      + generalize (type_check_store_spec2 _ _ _ _ _ htype_check_store heqTfetch0).
        intro hh.
        decomp hh.
        exists x0;simpl.
        rewrite heqfetch.
        auto.
      + Rinversion fetch.
    - specialize (IHh1 heqTfetchG0).
      decomp IHh1.
      exists x0.
      simpl.
      generalize (type_check_store_spec2_none _ _ _ htype_check_store heqTfetch).
      intros hhh.
      rewrite hhh.
      auto.
Qed.       
