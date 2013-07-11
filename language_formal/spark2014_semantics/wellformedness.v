Require Export environment.
Require Export semantics.

(** * Well-Formed Program  *)
(**
   Before executing the program, make sure that the program is well-formed
   - well-typed
      - all operators work on the operands of the right types;
      - all assignments write into memory with the values of right types;
      - variables has right _in/out_ mode;
   - well-defined 
      - all variables are initialized before they are used
   - well-checked
      - right checks are put at the right places
*)

(** this is used by the type system to check whether types are consistent on both sides
     of binary operators, and return either the result type or None if their types are not consistent
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
   - general type check for expressions;
   - all variables used in expression should be in mode _in_ or _in/out_; 
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
   - _in/out_ mode checking (for variables that are updated by assignments, their mode should be _out_ or _in\out_);
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

(** Well-Defined means that all referenced variables are initialized *)
(** the initialization modes can be either Init (initialized) or Uninit (uninitialized) *)
Inductive init_mode: Type := 
    | Init: init_mode
    | Uninit: init_mode.

Definition initializationState: Type := list (idnum * init_mode).

(** basic functions for fetching and updating the variable's initialization state *)
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
(** 
    update by assignment will make the uninitialized variables into initialized one, so 
    in the following definition, we have to track the initialization states after executing
    each command, and use the latest initialization state to check whether the used variables 
    are initialized or not;
    For conditional and while loop commands, their final initialization state are the intersection 
    of the resulting initialization states from both branches;
*)
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

(** ** Lemmas for fetching and updating initialization state *)
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
(** 
   for any variable in stack, if it has a defined value then it has an initialized state,
   otherwise, it's uninitialized;
*)
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
(** 
    'istate' is an initialization state map (from variable to initialization mode: Init or Uninit) that's constructed
    from the stack 's' (mapping from variable to defined value or undefined value);
    when we fetch a variable 'x' from stack 's', if it returns some value 'v', then the result should be the 'Init' mode 
    when we fetch it from the corresponding initialization state map 'istate';
*)
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

(** the reverse is the same *)
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

(** for any stack s, we can only compute one initialization state Map from s *)
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

(** when we update the stack s with x by a new value v, the initialization state map istate'1 computed
     from s1 should be equal to the initialization state istate1 that update istate with x by Init directly;
*)
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


(* = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = *)

(** * Well-Checked *)
(** get the ast id from the expression ast node *)
Definition get_ast_id_expr (e: expr): astnum :=
    match e with
    | (Econst ast_id n) => ast_id
    | (Evar ast_id x) => ast_id
    | (Ebinop ast_id op e1 e2) => ast_id
    | (Eunop ast_id op e) => ast_id
    end.

(** get the ast id from the statemet ast node *)
Definition get_ast_id_stmt (c: stmt): astnum :=
    match c with
    | (Sassign ast_id x e) => ast_id
    | (Sseq ast_id c1 c2) => ast_id
    | (Sifthen ast_id b c) => ast_id
    | (Swhile ast_id b c) => ast_id
    end.

Definition max_id := astnum.

(** ast_id for each AST node is unique *)
(** later the ast id will be used to map ast node to the check flag denoting the run-time checks
     that needs to be performed before executing that ast node;
*)

(** all the ast ids for expression ast nodes are unique: parent node's ast id number is smaller than
     children node's ast id number, and the left child node's id number is smaller than the right child 
     node's id number; max_id is the maximum ast id number used in the expression
*)
Inductive ast_id_inc_expr: expr -> max_id -> Prop :=
    | Inc_Econst: forall ast_id n,
        ast_id_inc_expr (Econst ast_id n) ast_id
    | Inc_Evar: forall ast_id x,
        ast_id_inc_expr (Evar ast_id x) ast_id
    | Inc_Ebinop: forall e1 max1 e2 max2 ast_id1 ast_id2 ast_id op,
        ast_id_inc_expr e1 max1 ->
        ast_id_inc_expr e2 max2 ->
        get_ast_id_expr e1 = ast_id1 ->
        get_ast_id_expr e2 = ast_id2 ->
        ast_id < ast_id1 ->
        ast_id < ast_id2 ->
        max1 < ast_id2 ->
        ast_id_inc_expr (Ebinop ast_id op e1 e2) max2
    | Inc_Eunop: forall e max ast_id0 ast_id op,
        ast_id_inc_expr e max ->
        get_ast_id_expr e = ast_id0 ->
        ast_id < ast_id0 ->
        ast_id_inc_expr (Eunop ast_id op e) max.

(** it's similar to ast_id_inc_expr, all ast id number is unique *)
Inductive ast_id_inc_stmt: stmt -> max_id -> Prop :=
    | Inc_Sassign: forall e max ast_id0 ast_id x,
        ast_id_inc_expr e max ->
        get_ast_id_expr e = ast_id0 ->
        ast_id < ast_id0 ->
        ast_id_inc_stmt (Sassign ast_id x e) max
    | Inc_Sseq: forall c1 max1 c2 max2 ast_id1 ast_id2 ast_id,
        ast_id_inc_stmt c1 max1 ->
        ast_id_inc_stmt c2 max2 ->
        get_ast_id_stmt c1 = ast_id1 ->
        get_ast_id_stmt c2 = ast_id2 ->
        ast_id < ast_id1 ->
        ast_id < ast_id2 ->
        max1 < ast_id2 ->
        ast_id_inc_stmt (Sseq ast_id c1 c2) max2
    | Inc_Sifthen: forall b max1 c max2 ast_id1 ast_id2 ast_id,
        ast_id_inc_expr b max1 ->
        ast_id_inc_stmt c max2 ->
        get_ast_id_expr b = ast_id1 ->
        get_ast_id_stmt c = ast_id2 ->
        ast_id < ast_id1 ->
        ast_id < ast_id2 ->
        max1 < ast_id2 ->
        ast_id_inc_stmt (Sifthen ast_id b c) max2
    | Inc_Swhile: forall b max1 c max2 ast_id1 ast_id2 ast_id,
        ast_id_inc_expr b max1 ->
        ast_id_inc_stmt c max2 ->
        get_ast_id_expr b = ast_id1 ->
        get_ast_id_stmt c = ast_id2 ->
        ast_id < ast_id1 -> 
        ast_id < ast_id2 -> 
        max1 < ast_id2 ->
        ast_id_inc_stmt (Swhile ast_id b c) max2.


(** ** Generate the run-time-check flags *)

(** the run-time checks are stored in a list indexed with ast id number *)
Definition check_points :=  list (astnum * check_action).

Function fetch_ck (id : astnum) (m : check_points): option check_action := 
    match m with 
    | (id0, ck0) :: s0 =>
      if beq_nat id id0 then
        Some ck0
      else 
        fetch_ck id s0 
    | nil => None
    end.

(** this's used to constrain that all ast id number used in check_points are smaller than a certain number *)
Inductive ast_ids_lt: check_points -> astnum -> Prop := 
    | lt1: forall ls n ast_id ck,
        ast_ids_lt ls n ->
        ast_id < n ->
        ast_ids_lt ((ast_id, ck) ::ls) n
    | lt2: forall n,
        ast_ids_lt nil n.

Lemma ast_ids_lt_trans0: forall ls n n',
    ast_ids_lt ls n ->
    n <= n' ->
    ast_ids_lt ls n'.
Proof.
    intros ls n n' h1 h2.
    induction h1.
  - constructor.
    apply IHh1; assumption.
    intuition.
  - constructor.    
Qed.

Lemma ast_ids_lt_trans: forall ls n n',
    ast_ids_lt ls n ->
    n < n' ->
    ast_ids_lt ls n'.
Proof.
    intros.
    eapply ast_ids_lt_trans0.
    apply H. 
    intuition.
Qed.


(** *** generate run-time-check flags for expressions *)
(** compute check flags for each expression ast node according to the checking rules, and the results  
     are stored in a list of type check_points
*)
Inductive check_generator_expr: check_points -> expr -> check_points -> Prop :=
    | CG_Econst: forall ast_id n flag ls,
        check_flag (Econst ast_id n) flag -> 
        check_generator_expr ls (Econst ast_id n) ((ast_id, flag ) :: ls)
    | CG_Evar: forall ast_id x flag ls,
        check_flag (Evar ast_id x) flag ->
        check_generator_expr ls (Evar ast_id x) ((ast_id, flag) :: ls)
    | CG_Ebinop: forall ls e1 ls1 e2 ls2 ast_id op flag,
        check_generator_expr ls e1 ls1 ->
        check_generator_expr ls1 e2 ls2 ->
        check_flag (Ebinop ast_id op e1 e2) flag -> 
        check_generator_expr ls (Ebinop ast_id op e1 e2) ((ast_id, flag) :: ls2)
    | CG_Eunop: forall ls e ls1 ast_id op flag,
        check_generator_expr ls e ls1 ->
        check_flag (Eunop ast_id op e) flag ->
        check_generator_expr ls (Eunop ast_id op e) ((ast_id, flag ) :: ls1).

(** *** generate run-time-check flags for statements *)
(** For the SPARK 2014 subset that we are working on, we only consider the division by zero check and 
     overflow check. So here, the check for each statement is none, but it is extensible to includes necessary 
     checks in the statements in the future. 
 *)
Inductive check_generator_stmt: check_points -> stmt -> check_points -> Prop :=
    | CG_Sassign: forall ls1 e ls2 ast_id x,
        check_generator_expr ls1 e ls2 ->
        check_generator_stmt ls1 (Sassign ast_id x e) ((ast_id, No_Check) :: ls2)
    | CG_Sseq: forall ls1 c1 ls2 c2 ls3 ast_id,
        check_generator_stmt ls1 c1 ls2 ->
        check_generator_stmt ls2 c2 ls3 ->
        check_generator_stmt ls1 (Sseq ast_id c1 c2) ((ast_id, No_Check) :: ls3)
    | CG_Sifthen: forall ls1 b ls2 c ls3 ast_id,
        check_generator_expr ls1 b ls2 ->
        check_generator_stmt ls2 c ls3 ->
        check_generator_stmt ls1 (Sifthen ast_id b c) ((ast_id, No_Check) :: ls3)
    | CG_Swhile: forall ls1 b ls2 c ls3 ast_id,
        check_generator_expr ls1 b ls2 ->
        check_generator_stmt ls2 c ls3 ->        
        check_generator_stmt ls1 (Swhile ast_id b c) ((ast_id, No_Check) :: ls3).

(** ** Semantics with run-time-checks *)
(** the semantics for expressions evaluation, where cps is passed in as a parameter telling 
     whether a check is needed to be performed before executing the expression ast node
*)
Inductive eval_expr_with_checks (cps: check_points): stack -> expr -> return_val -> Prop :=
    | eval_Const: forall cst v s ast_id,
        eval_constant cst = v ->
        eval_expr_with_checks cps s (Econst ast_id cst) v
    | eval_Var: forall x s v ast_id,
        fetch x s = Some v ->
        eval_expr_with_checks cps s (Evar ast_id x) (ValNormal v)
    | eval_Binop1: forall s e1 ast_id op e2,
        eval_expr_with_checks cps s e1 ValException ->
        eval_expr_with_checks cps s (Ebinop ast_id op e1 e2) ValException
    | eval_Binop2: forall s e1 v1 e2 ast_id op,
        eval_expr_with_checks cps s e1 (ValNormal v1) ->
        eval_expr_with_checks cps s e2 ValException ->
        eval_expr_with_checks cps s (Ebinop ast_id op e1 e2) ValException
    | eval_Binop3: forall s e1 v1 e2 v2 ck ast_id op,
        eval_expr_with_checks cps s e1 (ValNormal v1) ->
        eval_expr_with_checks cps s e2 (ValNormal v2) ->
        fetch_ck ast_id cps = Some ck -> 
        do_check (eval_expr_with_checks cps) s ck false ->
        eval_expr_with_checks cps s (Ebinop ast_id op e1 e2) ValException
    | eval_Binop4: forall s e1 v1 e2 v2 ck ast_id op v,
        eval_expr_with_checks cps s e1 (ValNormal v1) ->
        eval_expr_with_checks cps s e2 (ValNormal v2) ->
        fetch_ck ast_id cps = Some ck -> 
        do_check (eval_expr_with_checks cps) s ck true ->
        eval_binop op (ValNormal v1) (ValNormal v2) = v ->
        v <> ValAbnormal ->
        eval_expr_with_checks cps s (Ebinop ast_id op e1 e2) v
    | eval_Unop1: forall s e ast_id op,
        eval_expr_with_checks cps s e ValException ->
        eval_expr_with_checks cps s (Eunop ast_id op e) ValException
    | eval_Unop2: forall s e v ast_id op v1,
        eval_expr_with_checks cps s e (ValNormal v) ->
        eval_unop op (ValNormal v) = v1 ->
        v1 <> ValAbnormal ->
        eval_expr_with_checks cps s (Eunop ast_id op e) v1.


(** 
    it's similar to the eval_expr_with_checks: cps is used to denote whether a check is needed to be
    performed before executing the statement; right now, we only consider the division and overflow checks
    for expressions, and there are checks enfornced on the statements
*)
Inductive eval_stmt_with_checks (cps: check_points): stack -> stmt -> state -> Prop :=
    | eval_Assign1: forall s e ast_id x,
        eval_expr_with_checks cps s e ValException ->
        eval_stmt_with_checks cps s (Sassign ast_id x e) SException
    | eval_Assign2: forall s e v x s1 ast_id,
        eval_expr_with_checks cps s e (ValNormal v) ->
        update s x (Value v) = Some s1 -> 
        eval_stmt_with_checks cps s (Sassign ast_id x e) (SNormal s1)
    | eval_Seq1: forall s c1 ast_id c2,
        eval_stmt_with_checks cps s c1 SException ->
        eval_stmt_with_checks cps s (Sseq ast_id c1 c2) SException
    | eval_Seq2: forall ast_id s s1 s2 c1 c2,
        eval_stmt_with_checks cps s c1 (SNormal s1) ->
        eval_stmt_with_checks cps s1 c2 s2 ->
        eval_stmt_with_checks cps s (Sseq ast_id c1 c2) s2
    | eval_Ifthen: forall s b ast_id c,
        eval_expr_with_checks cps s b ValException ->
        eval_stmt_with_checks cps s (Sifthen ast_id b c) SException
    | eval_Ifthen_True: forall s b c s1 ast_id,
        eval_expr_with_checks cps s b (ValNormal (Bool true)) ->
        eval_stmt_with_checks cps s c s1 ->
        eval_stmt_with_checks cps s (Sifthen ast_id b c) s1
    | eval_Ifthen_False: forall s b ast_id c,
        eval_expr_with_checks cps s b (ValNormal (Bool false)) ->
        eval_stmt_with_checks cps s (Sifthen ast_id b c) (SNormal s)
    | eval_While: forall s b ast_id c,
        eval_expr_with_checks cps s b ValException ->
        eval_stmt_with_checks cps s (Swhile ast_id b c) SException
    | eval_While_True1: forall s b c ast_id,
        eval_expr_with_checks cps s b (ValNormal (Bool true)) ->
        eval_stmt_with_checks cps s c SException ->
        eval_stmt_with_checks cps s (Swhile ast_id b c) SException
    | eval_While_True2: forall s b c s1 ast_id s2,
        eval_expr_with_checks cps s b (ValNormal (Bool true)) ->
        eval_stmt_with_checks cps s c (SNormal s1) ->
        eval_stmt_with_checks cps s1 (Swhile ast_id b c) s2 ->
        eval_stmt_with_checks cps s (Swhile ast_id b c) s2
    | eval_While_False: forall s b ast_id c,
        eval_expr_with_checks cps s b (ValNormal (Bool false)) ->
        eval_stmt_with_checks cps s (Swhile ast_id b c) (SNormal s).


(** some basic lemmas *)
(** eval_stmt_with_checks returns either a normal value or an exception when the check is false *)
Lemma eval_expr_with_checks_state: forall ls s e v,
    eval_expr_with_checks ls s e v ->
    (exists v0, v = ValNormal v0) \/ v = ValException.
Proof.
    intros.
    induction H;
    try match goal with
    | [ |- (exists v0 : value, ValNormal v = ValNormal v0) \/ _ ] => left; exists v; reflexivity
    | [ |- _ \/ ?A = ?A ] => right; reflexivity
    end.
  - destruct cst; simpl in H; rewrite <- H;
    left; 
    [exists (Int z) | exists (Bool b)]; reflexivity.
  - destruct v.
    left; exists v; reflexivity.
    right; reflexivity.
    intuition.
  - destruct v1.
    left; exists v0; reflexivity.
    right; reflexivity.
    intuition.    
Qed.

(** the results of running eval_expr_with_checks should be unique *)
Lemma eval_expr_with_checks_unique: forall ls s e v1 v2,
    eval_expr_with_checks ls s e (ValNormal v1) ->
    eval_expr_with_checks ls s e (ValNormal v2) ->
    v1 = v2.
Proof.
    induction e;
    intros v1 v2 h1 h2;
    inversion h1; subst;
    inversion h2; subst.
  - rewrite H3 in H4.
    inversion H4; subst;
    reflexivity.
  - rewrite H1 in H2; inversion H2; subst; 
    reflexivity.
  - specialize (IHe1 _ _ H3 H5).
    specialize (IHe2 _ _ H4 H7). subst.
    rewrite H15 in H9; inversion H9; subst.
    reflexivity.
  - specialize (IHe _ _ H1 H2).
    subst. 
    destruct op0, op.
    rewrite H6 in H3; inversion H3; subst;
    auto.
Qed.

(*
Lemma eval_expr_with_checks_unique: forall ls s e v1 v2,
    eval_expr_with_checks ls s e v1 ->
    eval_expr_with_checks ls s e v2 ->
    v1 = v2.
Proof.
    induction e;
    intros v1 v2 h1 h2.
  - inversion h1; subst. 
    inversion h2; subst.
    reflexivity.
  - inversion h1; subst. 
    inversion h2; subst.
    rewrite H3 in H4; inversion H4; subst; reflexivity.
  - inversion h1; subst.
    inversion h2; subst; auto;
    repeat match goal with
    | [ h1:  forall v1 v2,
               eval_expr_with_checks ?ls ?s ?e v1 ->
               eval_expr_with_checks ?ls ?s ?e v2 -> v1 = v2, 
        h2: eval_expr_with_checks ?ls ?s ?e ?x,
        h3: eval_expr_with_checks ?ls ?s ?e ?y |- _ ] => specialize (h1 _ _ h2 h3); inversion h1; subst
    end; auto.
    rewrite H7 in H10. inversion H10; subst. 
    clear IHe2 IHe1 H6 H4 H10.
    
    inversion H8; subst.
    inversion H8; subst.
    inversion H12; subst.   
    
    - inversion h1; subst;
      inversion h2; subst; auto;
      match goal with
      | [ h1:  forall v1 v2,
               eval_expr_with_checks ?ls ?s ?e v1 ->
               eval_expr_with_checks ?ls ?s ?e v2 -> v1 = v2, 
        h2: eval_expr_with_checks ?ls ?s ?e ?x,
        h3: eval_expr_with_checks ?ls ?s ?e ?y |- _ ] => specialize (h1 _ _ h2 h3); inversion h1; subst
    end; auto.
    destruct op, op0; auto.
Qed.
*)

(** 
   the ast id number is increasing: parent node's ast id number is smaller than children node's ast id number.
   (get_ast_id_expr e) is the ast id number for expression e, and max is the maximum ast id number used 
   by e. if e has no subexpression, then max is the same as (get_ast_id_expr e), otherwise, max is maximum
   ast id number of its subexpressions, so (get_ast_id_expr e) should be less and equal max
*)
Lemma ast_id_bound_expr: forall e max,
    ast_id_inc_expr e max ->
    get_ast_id_expr e <= max.
Proof.
    intros e max h.
    induction h; simpl; intuition.
Qed.

(** 
    checks are computed according to the checking rules for expression e and its subexpressions,
    the results are stored in cks indexed by expression and its subexpression ast ids,
    because max is the maximum ast id, so all ast ids in cks should be less than (max + 1)
*)
Lemma ast_id_max_expr: forall e max cks0 cks,
    ast_id_inc_expr e max ->
    check_generator_expr cks0 e cks ->
    ast_ids_lt cks0 (get_ast_id_expr e) ->
    ast_ids_lt cks (max + 1).
Proof.
    intros e max cks0 cks h1.
    revert cks0 cks.
    induction h1;
    intros cks0 cks h2 h3;
    simpl in h3; inversion h2; subst.
  - constructor.
    apply ast_ids_lt_trans with (n := ast_id); intuition.
    intuition.
  - constructor.
    apply ast_ids_lt_trans with (n := ast_id); intuition.
    intuition.
  - specialize (ast_ids_lt_trans _ _ _ h3 H1); intros hz1.
    specialize (ast_ids_lt_trans _ _ _ h3 H2); intros hz2.
    specialize (IHh1_1 _ _ H10 hz1).
    assert(hz: max1 + 1 <= get_ast_id_expr e2); intuition.
    specialize (ast_ids_lt_trans0 _ _ _ IHh1_1 hz); intros hz3.
    specialize (IHh1_2 _ _ H11 hz3).
    constructor.
    + assumption.
    + specialize (ast_id_bound_expr _ _ h1_2); intros hz4.
       intuition.
  - specialize (ast_ids_lt_trans _ _ _ h3 H0); intros hz1.
    specialize (IHh1 _ _ H4 hz1).
    constructor.
    + assumption.
    + specialize (ast_id_bound_expr _ _ h1); intros hz2.
       intuition.
Qed.

(** it's similar to ast_id_bound_expr *)
Lemma ast_id_bound_stmt: forall c max,
    ast_id_inc_stmt c max ->
    get_ast_id_stmt c <= max.
Proof.
    intros c max h.
    induction h; simpl; intuition.
    specialize (ast_id_bound_expr _ _ H); intros hz1.
    intuition.    
Qed.

(** it's similar to ast_id_max_expr *)
Lemma ast_id_max_stmt: forall c max cks0 cks1,
    ast_id_inc_stmt c max ->
    check_generator_stmt cks0 c cks1 ->
    ast_ids_lt cks0 (get_ast_id_stmt c) ->
    ast_ids_lt cks1 (max + 1).
Proof.
    intros c max cks0 cks1 h1.
    revert cks0 cks1.
    induction h1;
    intros cks0 cks1 h2 h3;
    simpl in h3; inversion h2; subst.
  - specialize (ast_ids_lt_trans _ _ _ h3 H1); intros hz1.
    specialize (ast_id_max_expr _ _ _ _ H H7 hz1); intros hz2.
    specialize (ast_id_bound_expr _ _ H); intros hz3.
    constructor; intuition.
  - specialize (ast_ids_lt_trans _ _ _ h3 H1); intros hz1.
    specialize (IHh1_1 _ _ H9 hz1).
    assert (hz: max1 + 1 <= get_ast_id_stmt c2); intuition.
    specialize (ast_ids_lt_trans0 _ _ _ IHh1_1 hz); intros hz2.
    specialize (IHh1_2 _ _ H10 hz2).
    constructor. assumption.
    specialize (ast_id_bound_stmt _ _ h1_2); intros hz3.
    intuition.
  - specialize (ast_ids_lt_trans _ _ _ h3 H2); intros hz1.
    specialize (ast_id_max_expr _ _ _ _ H H10 hz1); intros hz2.
    assert (hz: max1 + 1 <= get_ast_id_stmt c); intuition.
    specialize (ast_ids_lt_trans0 _ _ _ hz2 hz); intros hz3.
    specialize (IHh1 _ _ H11 hz3).
    constructor. assumption.
    specialize (ast_id_bound_stmt _ _ h1); intros hz4.
    intuition.
  - specialize (ast_ids_lt_trans _ _ _ h3 H2); intros hz1.
    specialize (ast_id_max_expr _ _ _ _ H H10 hz1); intros hz2.
    assert (hz: max1 + 1 <= get_ast_id_stmt c); intuition.
    specialize (ast_ids_lt_trans0 _ _ _ hz2 hz); intros hz3.
    specialize (IHh1 _ _ H11 hz3).
    constructor. assumption.
    specialize (ast_id_bound_stmt _ _ h1); intros hz4.
    intuition.
Qed.














