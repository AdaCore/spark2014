Require Export semantics. 

(** * Well-Formed Program  *)
(**
   Before executing the program, make sure that the program is well-formed
   - well-typed: 
      - all operators work on the operands of the right types;
      - all assignments write into memory with the values of right types;
      - variables has right _in/out_ mode;
   - well-defined: 
      all variables are initialized before they are used
*)

Definition binop_type (op: binary_operation) (x y: typ): option typ := 
    match op with 
    | Ceq | Cne  => 
        match x, y with
        | Tint, Tint => Some Tbool
        | _, _ => None
        end
    | Oand | Oor =>
        match x, y with
        | Tbool, Tbool => Some Tbool
        | _, _ => None
        end
    | Oadd | Osub | Omul | Odiv =>
        match x, y with
        | Tint, Tint => Some Tint
        | _, _ => None
        end
    end.

(** * Well-Typed *)
(** ** Well-typed expressions *)
(**
   - general type checking;
   - all variables should be in mode _in_; 
*)
Inductive well_typed_expr: symtb -> expr -> typ -> Prop :=
    | WT_Econst_Int: forall ast_id n tb,
        well_typed_expr tb (Econst ast_id (Ointconst n)) Tint
    | WT_Econst_Bool: forall ast_id b tb,
        well_typed_expr tb (Econst ast_id (Oboolconst b)) Tbool
    | WT_Evar: forall ast_id x tb t,
        lookup x tb = Some (In, t) ->  (* the 'out' variables can never be read *)    
        well_typed_expr tb (Evar ast_id x) t
    | WT_Ebinop: forall ast_id tb op e1 e2 t t1,
        well_typed_expr tb e1 t ->
        well_typed_expr tb e2 t ->
        binop_type op t t = Some t1 ->
        well_typed_expr tb (Ebinop ast_id op e1 e2) t1
    | WT_Eunop: forall ast_id tb op e,
        well_typed_expr tb e Tbool ->
        well_typed_expr tb (Eunop ast_id op e) Tbool.


(** ** Well-typed commands *)
(**
   two kinds of type checking:
   - general type checking;
   - _in/out_ mode checking;
*)
Inductive well_typed_stmt: symtb -> stmt  -> Prop :=
    | WT_Sassign: forall ast_id tb x e t,
        lookup x tb = Some (Out, t) ->
        well_typed_expr tb e t ->
        well_typed_stmt tb ((Sassign ast_id x e))
    | WT_Sseq: forall ast_id c1 c2 tb,
        well_typed_stmt tb c1 ->
        well_typed_stmt tb c2 ->
        well_typed_stmt tb (Sseq ast_id c1 c2)
    | WT_Sifthen: forall ast_id tb b c,
        well_typed_expr tb b Tbool ->
        well_typed_stmt tb c ->
        well_typed_stmt tb (Sifthen ast_id b c)
    | WT_Swhile: forall ast_id tb b c,
        well_typed_expr tb b Tbool ->
        well_typed_stmt tb c ->
        well_typed_stmt tb (Swhile ast_id b c).
(*    | WT_Sassert: forall ast_id tb e, 
        well_typed_expr tb e Tbool ->
        well_typed_stmt tb (Sassert ast_id e) *)

(* =============================== *)

(** * Well-Defined *)

(** basic data structures for well-defined expressions and commands *)
Inductive init_mode: Type := 
    | Init: init_mode
    | Uninit: init_mode.

Definition initializationState: Type := list (idnum * init_mode).

(** basic operators for well-defined expressions and commands *)
Function fetch2 (x : idnum) (s : initializationState): option init_mode := 
    match s with 
    | (y, imode) :: s' =>
      if beq_nat x y then
        Some imode
      else fetch2 x s' 
    | nil => None
    end.

Function update2 (s: initializationState) (x : idnum) (v: init_mode): option initializationState := 
    match s with 
    | (y, imode) :: s' => 
      if beq_nat x y then 
        Some ((y,v)::s') 
      else 
        match update2 s' x v with
        | Some s'' => Some ((y, imode)::s'')
        | None => None
        end
   | nil => None
   end.

(** ** Well-defined expressions *)
(**
    all referenced variables are initialized 
*)
Inductive well_defined_expr: initializationState -> expr -> Prop :=
    | WD_Econst_Int: forall ast_id s n,
        well_defined_expr s (Econst ast_id (Ointconst n))
    | WD_Econst_Bool: forall ast_id s b,
        well_defined_expr s (Econst ast_id (Oboolconst b))
    | WD_Evar: forall ast_id x s,
        fetch2 x s = Some Init ->
        well_defined_expr s (Evar ast_id x)
    | WD_Ebinop: forall ast_id s op e1 e2,
        well_defined_expr s e1 ->
        well_defined_expr s e2 ->
        well_defined_expr s (Ebinop ast_id op e1 e2)
    | WD_Eunop: forall ast_id s op e,
        well_defined_expr s e ->
        well_defined_expr s (Eunop ast_id op e). 

(*
Inductive well_defined_expr: stack -> expr -> Prop :=
    | WD_Econst_Int: forall ast_id s n,
        well_defined_expr s (Econst ast_id (Ointconst n))
    | WD_Econst_Bool: forall ast_id s b,
        well_defined_expr s (Econst ast_id (Oboolconst b))
    | WD_Evar: forall ast_id x v s,
        fetch x s = Some v ->
        well_defined_expr s (Evar ast_id x)
    | WD_Ebinop: forall ast_id s op e1 e2,
        well_defined_expr s e1 ->
        well_defined_expr s e2 ->
        well_defined_expr s (Ebinop ast_id op e1 e2)
    | WD_Eunop: forall ast_id s op e,
        well_defined_expr s e ->
        well_defined_expr s (Eunop ast_id op e). 
*)

(** ** Well-defined commands *)
Inductive well_defined_stmt: initializationState -> stmt -> initializationState -> Prop :=
    | WD_Sassign: forall ast_id s s' x e,
        well_defined_expr s e ->
        update2 s x Init = Some s' ->
        well_defined_stmt s (Sassign ast_id x e) s'
    | WD_Sseq: forall ast_id c1 c2 s s' s'',
        well_defined_stmt s c1 s' ->
        well_defined_stmt s' c2 s'' ->
        well_defined_stmt s (Sseq ast_id c1 c2) s''
    | WD_Sifthen: forall ast_id s s' b c,
        well_defined_expr s b ->
        well_defined_stmt s c s' ->
        well_defined_stmt s (Sifthen ast_id b c) s
    | WD_Swhile: forall ast_id s s' b c,
        well_defined_expr s b ->
        well_defined_stmt s c s' ->
        well_defined_stmt s (Swhile ast_id b c) s.

(** ** Lemmas about initialization operations *)
Lemma update2_fetch2: forall istate x m istate',
    update2 istate x m = Some istate' ->
    exists m0, fetch2 x istate = Some m0.
Proof.
    intros istate x m.
    functional induction (update2 istate x m);
    intros istate' h1.
  - unfold fetch2.
    rewrite e0.
    exists imode; auto.
  - unfold fetch2.
    rewrite e0.
    fold fetch2.
    specialize (IHo _ e1); assumption.
  - inversion h1.
  - inversion h1.
Qed.

Lemma fetch2_update2: forall x istate m0 m,
    fetch2 x istate = Some m0 ->
    exists istate', update2 istate x m = Some istate'.
Proof.
    intros x istate.
    functional induction (fetch2 x istate);
    intros m0 m h1.
  - unfold update2.
    rewrite e0.
    exists ((y, m) :: s'); auto.
  - unfold update2. 
    rewrite e0.
    fold update2.
    specialize (IHo _ m h1).
    inversion IHo.
    rewrite H.
    exists ((y, imode) :: x0); auto.
  - inversion h1.
Qed.

Lemma update2_in: forall istate x m istate' y m',
    update2 istate x m = Some istate' ->
    fetch2 y istate = Some m' ->
    (fetch2 y istate' = Some m) \/ (fetch2 y istate' = Some m').
Proof.
    intros istate x m.
    functional induction (update2 istate x m);
    intros istate' y0 m' h1 h2.
  - inversion h1; subst.
    unfold fetch2.
    unfold fetch2 in h2.
    destruct (beq_nat y0 y).
    + left; auto.
    + fold fetch2.
       fold fetch2 in h2.
       right; assumption.
  - inversion h1; subst.
    unfold fetch2.
    unfold fetch2 in h2.
    destruct (beq_nat y0 y).
    + right; assumption.
    + fold fetch2.
       fold fetch2 in h2.
       specialize (IHo _ _ _ e1 h2).
       assumption.
  - inversion h1.
  - inversion h1.
Qed.

Lemma update2_in1: forall istate x m istate' y m',
    update2 istate x m = Some istate' ->
    fetch2 y istate' = Some m' ->
    (y = x /\ m' = m) \/ (y <> x /\ fetch2 y istate = Some m').
Proof.
    intros istate x m.
    functional induction (update2 istate x m);
    intros istate' y0 m' h1 h2.
  - inversion h1; subst.
    unfold fetch2.
    unfold fetch2 in h2.
    remember (beq_nat y0 y) as eq.
    destruct eq.
    + left. 
       inversion h2; subst.
       apply beq_nat_true in e0.
       symmetry in Heqeq.
       apply beq_nat_true in Heqeq.
       subst. auto.
    + right. 
       fold fetch2.
       fold fetch2 in h2.
       symmetry in Heqeq.
       apply beq_nat_true in e0.
       apply beq_nat_false in Heqeq.
       subst.
       split; assumption.
  - inversion h1; subst.
    unfold fetch2.
    unfold fetch2 in h2.
    remember (beq_nat y0 y) as eq.
    destruct eq.
    + right.
       symmetry in Heqeq.
       apply beq_nat_false in e0;
       apply beq_nat_true in Heqeq; subst.
       split; auto.
    + fold fetch2.
       fold fetch2 in h2.
       specialize (IHo _ _ _ e1 h2).
       assumption.
  - inversion h1.
  - inversion h1.  
Qed.

Lemma update2_fetch2_new: forall istate x m istate',
    update2 istate x m = Some istate' ->
    fetch2 x istate' = Some m.
Proof.
    intros istate x m.
    functional induction (update2 istate x m);
    intros istate' h1.
  - inversion h1; subst.
    unfold fetch2.
    destruct (beq_nat x y).
    + auto.
    + inversion e0.
  - inversion h1; subst.
    unfold fetch2.
    destruct (beq_nat x y).
    + inversion e0.
    + fold fetch2.
       specialize (IHo _ e1).
       assumption.
  - inversion h1.
  - inversion h1.    
Qed.

Lemma update2_fetch2_old: forall istate x m istate' y,
    update2 istate x m = Some istate' ->
    y <> x ->
    fetch2 y istate' = fetch2 y istate.
Proof.
    intros istate x m.
    functional induction (update2 istate x m);
    intros istate' y0 h1 h2.
  - inversion h1; subst.
    apply beq_nat_true in e0.
    subst.
    apply beq_nat_false_iff in h2.
    unfold fetch2.
    rewrite h2.
    fold fetch2.
    auto.
  - inversion h1; subst.
    specialize (IHo _ _ e1 h2).
    unfold fetch2.
    destruct (beq_nat y0 y).
    auto.
    fold fetch2.
    assumption.
  - inversion h1.
  - inversion h1.    
Qed.

(** ** Mapping from stack to initialization state *)
Inductive initializationMap: stack -> initializationState -> Prop :=
    | IEmpty: initializationMap nil nil 
    | IList0: forall s ilist x v,
        v <> Vundef ->
        initializationMap s ilist ->
        initializationMap ((x, v)::s) ((x, Init)::ilist)
    | IList1: forall s ilist x v,
        v = Vundef ->
        initializationMap s ilist ->
        initializationMap ((x, v)::s) ((x, Uninit)::ilist).

(** some useful lemmas *)
Lemma initializationMap_consistent1: forall s istate x v,
    initializationMap s istate -> 
    fetch x s = Some v -> 
    fetch2 x istate = Some Init.
Proof.
    intros s istate x v h1 h2.
    induction h1.
      + inversion h2.
      + unfold fetch in h2. 
         unfold fetch2.
         destruct (beq_nat x x0); auto.
      + unfold fetch in h2.
         unfold fetch2.
         destruct (beq_nat x x0);
         auto.
         destruct v0.
         inversion H.
         inversion h2.
Qed.

Lemma initializationMap_consistent2: forall s istate x,
    initializationMap s istate ->
    fetch2 x istate = Some Init -> 
    exists v, fetch x s = Some v.
Proof.
    intros s istate x h1 h2.
    induction h1.
      + inversion h2.
      + unfold fetch2 in h2. 
         unfold fetch.
         destruct (beq_nat x x0); auto.
         destruct v.
         exists v; auto.
         intuition.
      + unfold fetch2 in h2.
         unfold fetch.
         destruct (beq_nat x x0); auto.
         destruct v.
         exists v; auto.
         inversion h2.    
Qed.


Lemma initializationMap_unique: forall s istate istate',
    initializationMap s istate ->
    initializationMap s istate' ->
    istate = istate'.
Proof.
    intros s istate istate' h1.
    generalize istate'. clear istate'.
    induction h1;
    intros istate' h2.
  - inversion h2.
    auto.
  - inversion h2; subst.
    specialize (IHh1 _ H5).
    subst. auto.
    intuition.
  - inversion h2; subst.
    intuition.
    specialize (IHh1 _ H5).
    subst.
    auto.
Qed.

Lemma update_consis: forall s istate x v s1 istate1 istate'1,
    initializationMap s istate -> 
    update s x (Value v) = Some s1 ->
    update2 istate x Init = Some istate1 ->
    initializationMap s1 istate'1 ->
    istate1 = istate'1.
Proof.
    intros s istate x v s1 istate1 istate'1 h1.
    generalize x v s1 istate1 istate'1.
    induction h1; intros.
  - inversion H.
  - unfold update in H0.
    unfold update2 in H1.
    destruct (beq_nat x1 x0).
    + inversion H0; subst.
       inversion H1; subst.
       inversion H2; subst.
       * specialize (initializationMap_unique _ _ _ h1 H8); intros hz1.
         subst.
         auto.
       * inversion H7.
    + fold update in H0.
       fold update2 in H1.
       remember (update s x1 (Value v1)) as eq1.
       remember (update2 ilist x1 Init) as eq2.
       destruct eq1; destruct eq2.
       * inversion H0; subst; clear H0.
         inversion H1; subst; clear H1.
         symmetry in Heqeq1. 
         symmetry in Heqeq2.
         inversion H2; subst.
         specialize (IHh1 _ _ _ _ _ Heqeq1 Heqeq2 H6).
         subst. auto.
         intuition.
       * inversion H1.
       * inversion H0.
       * inversion H0.
  - unfold update in H0.
    unfold update2 in H1.
    destruct (beq_nat x1 x0).
    + inversion H0; subst.
       inversion H1; subst.
       inversion H2; subst.
       * specialize (initializationMap_unique _ _ _ h1 H7); intros hz1.
         subst.
         auto.
       * inversion H6.
    + fold update in H0.
       fold update2 in H1.
       remember (update s x1 (Value v1)) as eq1.
       remember (update2 ilist x1 Init) as eq2.
       destruct eq1; destruct eq2.
       * inversion H0; subst; clear H0.
         inversion H1; subst; clear H1.
         symmetry in Heqeq1. 
         symmetry in Heqeq2.
         inversion H2; subst.
         intuition.
         specialize (IHh1 _ _ _ _ _ Heqeq1 Heqeq2 H5).
         subst. auto.
       * inversion H1.
       * inversion H0.
       * inversion H0.
Qed.














