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
*)
Inductive well_typed_expr: symtb -> expr -> typ -> Prop :=
    | WT_Econst_Int: forall ast_num n tb,
        well_typed_expr tb (Econst ast_num (Ointconst n)) Tint
    | WT_Econst_Bool: forall ast_num b tb,
        well_typed_expr tb (Econst ast_num (Oboolconst b)) Tbool
    | WT_Evar: forall ast_num x tb m t,
        lookup x tb = Some (m, t) ->  
        well_typed_expr tb (Evar ast_num x) t
    | WT_Ebinop: forall ast_num tb op e1 e2 t t1,
        well_typed_expr tb e1 t ->
        well_typed_expr tb e2 t ->
        binop_type op t t = Some t1 ->
        well_typed_expr tb (Ebinop ast_num op e1 e2) t1
    | WT_Eunop: forall ast_num tb op e,
        well_typed_expr tb e Tbool ->
        well_typed_expr tb (Eunop ast_num op e) Tbool.


(** ** Well-typed commands *)
(**
    - general type checking;
*)
Inductive well_typed_stmt: symtb -> stmt  -> Prop :=
    | WT_Sassign: forall ast_num tb x e m t,
        lookup x tb = Some (m, t) ->
        well_typed_expr tb e t ->
        well_typed_stmt tb ((Sassign ast_num x e))
    | WT_Sseq: forall ast_num c1 c2 tb,
        well_typed_stmt tb c1 ->
        well_typed_stmt tb c2 ->
        well_typed_stmt tb (Sseq ast_num c1 c2)
    | WT_Sifthen: forall ast_num tb b c,
        well_typed_expr tb b Tbool ->
        well_typed_stmt tb c ->
        well_typed_stmt tb (Sifthen ast_num b c)
    | WT_Swhile: forall ast_num tb b c,
        well_typed_expr tb b Tbool ->
        well_typed_stmt tb c ->
        well_typed_stmt tb (Swhile ast_num b c).

(* =============================== *)

(** * Well-Defined *)

(** Well-Defined means that all referenced variables are initialized *)
(** the initialization modes can be either Init (initialized) or Uninit (uninitialized) *)
Inductive init_mode: Type := 
    | Init: init_mode
    | Uninit: init_mode.

(** map from variable to its initialization state and in/out mode *)
Definition mode_map: Type := list (idnum * (init_mode * mode)).

(** basic functions for fetching and updating the variable's initialization state *)
Function fetch2 (x : idnum) (s : mode_map): option (init_mode * mode) := 
    match s with 
    | (y, m) :: s' =>
      if beq_nat x y then
        Some m
      else fetch2 x s' 
    | nil => None
    end.

Function update2 (s: mode_map) (x : idnum) (m: (init_mode * mode)): option mode_map := 
    match s with 
    | (y, m0) :: s' => 
      if beq_nat x y then 
        Some ((y,m)::s') 
      else 
        match update2 s' x m with
        | Some s'' => Some ((y, m0)::s'')
        | None => None
        end
   | nil => None
   end.

(** ** Well-defined expressions *)
(**
   - all referenced variables are initialized 
   - all variables used in expression should be in mode _in_ or _in/out_; 
*)
Inductive well_defined_expr: mode_map -> expr -> Prop :=
    | WD_Econst_Int: forall ast_num m n,
        well_defined_expr m (Econst ast_num (Ointconst n))
    | WD_Econst_Bool: forall ast_num m b,
        well_defined_expr m (Econst ast_num (Oboolconst b))
    | WD_Evar: forall ast_num x m md,
        fetch2 x m = Some (Init, md) -> (* initialized out variables can also be read *)
        well_defined_expr m (Evar ast_num x)
    | WD_Ebinop: forall ast_num m op e1 e2,
        well_defined_expr m e1 ->
        well_defined_expr m e2 ->
        well_defined_expr m (Ebinop ast_num op e1 e2)
    | WD_Eunop: forall ast_num m op e,
        well_defined_expr m e ->
        well_defined_expr m (Eunop ast_num op e). 


(** ** Well-defined commands *)
(** 
    update by assignment will make the uninitialized variables into initialized one, so 
    in the following definition, we have to track the initialization states after executing
    each command, and use the latest initialization state to check whether the used variables 
    are initialized or not;
    For conditional and while loop commands, their final initialization state are the intersection 
    of the resulting initialization states from both branches;
   - _in/out_ mode checking (for variables that are updated by assignments, their mode should be _out_ or _in\out_);
*)

Inductive well_defined_stmt: mode_map -> stmt -> mode_map -> Prop :=
    | WD_Sassign: forall m e x i md m' ast_num,
        well_defined_expr m e ->
        fetch2 x m = Some (i, md) ->
        md <> In ->
        update2 m x (Init, md) = Some m' ->
        well_defined_stmt m (Sassign ast_num x e) m'
    | WD_Sseq: forall ast_num c1 c2 m m' m'',
        well_defined_stmt m c1 m' ->
        well_defined_stmt m' c2 m'' ->
        well_defined_stmt m (Sseq ast_num c1 c2) m''
    | WD_Sifthen: forall ast_num m m' b c,
        well_defined_expr m b ->
        well_defined_stmt m c m' ->
        well_defined_stmt m (Sifthen ast_num b c) m
    | WD_Swhile: forall ast_num m m' b c,
        well_defined_expr m b ->
        well_defined_stmt m c m' ->
        well_defined_stmt m (Swhile ast_num b c) m.

(** ** Lemmas for fetching and updating initialization state *)
Lemma update2_fetch2: forall s x m s',
    update2 s x m = Some s' ->
    exists m0, fetch2 x s = Some m0.
Proof.
    intros s x m.
    functional induction (update2 s x m);
    intros s'0 h1.
  - unfold fetch2.
    rewrite e0.
    exists m0; auto.
  - unfold fetch2.
    rewrite e0.
    fold fetch2.
    specialize (IHo _ e1); assumption.
  - inversion h1.
  - inversion h1.
Qed.

Lemma fetch2_update2: forall x s m0 m,
    fetch2 x s = Some m0 ->
    exists s', update2 s x m = Some s'.
Proof.
    intros x s.
    functional induction (fetch2 x s);
    intros m0 m1 h1.
  - unfold update2.
    rewrite e0.
    exists ((y, m1) :: s'); auto.
  - unfold update2. 
    rewrite e0.
    fold update2.
    specialize (IHo _ m1 h1).
    inversion IHo.
    rewrite H.
    exists ((y, m) :: x0); auto.
  - inversion h1.
Qed.

Lemma update2_in: forall s x m s' y m',
    update2 s x m = Some s' ->
    fetch2 y s = Some m' ->
    (fetch2 y s' = Some m) \/ (fetch2 y s' = Some m').
Proof.
    intros s x m.
    functional induction (update2 s x m);
    intros s'0 y0 m' h1 h2.
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

Lemma update2_in1: forall s x m s' y m',
    update2 s x m = Some s' ->
    fetch2 y s' = Some m' ->
    (y = x /\ m' = m) \/ (y <> x /\ fetch2 y s = Some m').
Proof.
    intros s x m.
    functional induction (update2 s x m);
    intros s'0 y0 m' h1 h2.
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

Lemma update2_fetch2_new: forall s x m s',
    update2 s x m = Some s' ->
    fetch2 x s' = Some m.
Proof.
    intros s x m.
    functional induction (update2 s x m);
    intros s'0 h1.
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

Lemma update2_fetch2_old: forall s x m s' y,
    update2 s x m = Some s' ->
    y <> x ->
    fetch2 y s' = fetch2 y s.
Proof.
    intros s x m.
    functional induction (update2 s x m);
    intros s'0 y0 h1 h2.
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

(** ** Constructing mode map mapping from variable id to (initialization state * in/out mode)  *)
(** 
   for any variable in stack, if it has a defined value then it has an initialized state,
   otherwise, it's uninitialized;
*)
Inductive mode_mapping: symtb -> stack -> (mode_map) -> Prop :=
    | M_Empty: mode_mapping nil nil nil
    | M_Bool: forall tb s x m b ls,
          mode_mapping tb s ls ->
          mode_mapping ((x, (m, Tbool)) :: tb) ((x, (Value (Bool b))) :: s) ((x, (Init, m)) :: ls)
    | M_Int: forall tb s x m v ls,
          mode_mapping tb s ls ->
          mode_mapping ((x, (m, Tint)) :: tb) ((x, (Value (Int v))) :: s) ((x, (Init, m)) :: ls)
    | M_UndefBool: forall tb s x m ls,
          mode_mapping tb s ls ->
          mode_mapping ((x, (m, Tbool)) :: tb) ((x, Vundef) :: s) ((x, (Uninit, m)) :: ls)
    | M_UndefInt: forall tb s x m ls,
          mode_mapping tb s ls ->
          mode_mapping ((x, (m, Tint)) :: tb) ((x, Vundef) :: s) ((x, (Uninit, m)) :: ls).

Lemma mode_mapping_unique: forall tb s m1 m2,
    mode_mapping tb s m1 ->
    mode_mapping tb s m2 ->
    m1 = m2.
Proof.
    intros tb s m1 m2 H.
    revert m2.
    induction H;
    intros m2 H0;
    inversion H0; subst.
  - reflexivity.
  - specialize (IHmode_mapping _ H7); subst.
    reflexivity.
  - specialize (IHmode_mapping _ H7); subst; 
    reflexivity.
  - specialize (IHmode_mapping _ H6); subst; 
    reflexivity.
  - specialize (IHmode_mapping _ H6); subst; 
    reflexivity.
Qed.


Lemma mode_mapping_exists: forall tb s,
    type_check_stack tb s ->
    exists m, mode_mapping tb s m.
Proof.
    intros.
    induction H;
    [ exists nil; constructor | | | | ];
    inversion IHtype_check_stack;
    [exists ((x, (Init, m)) :: x0) | exists ((x, (Init, m)) :: x0) | 
     exists ((x, (Uninit, m)) :: x0) | exists ((x, (Uninit, m)) :: x0)
    ]; constructor; assumption.
Qed.

Lemma fetch_exists: forall tb s m x y,
    mode_mapping tb s m ->
    fetch2 x m = Some (Init, y) ->
    exists v, fetch x s = Some v.
Proof. 
    intros tb s m x y h1 h2.
    induction h1.
  - inversion h2.
  - unfold fetch2 in h2.
    unfold fetch.
    destruct (beq_nat x x0).
    exists (Bool b); reflexivity.
    fold fetch. fold fetch2 in h2.
    apply IHh1; assumption.
  - unfold fetch2 in h2.
    unfold fetch.
    destruct (beq_nat x x0).
    exists (Int v); reflexivity.
    fold fetch. fold fetch2 in h2.
    apply IHh1; assumption.
  - unfold fetch2 in h2.
    unfold fetch.
    destruct (beq_nat x x0).
    inversion h2.
    fold fetch. fold fetch2 in h2.
    apply IHh1; assumption.
  - unfold fetch2 in h2.
    unfold fetch.
    destruct (beq_nat x x0).
    inversion h2.
    fold fetch. fold fetch2 in h2.
    apply IHh1; assumption.
Qed.



(* = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = *)

(** * Well-Checked *)
(** get the ast number from the expression ast node *)
Definition get_ast_num_expr (e: expr): astnum :=
    match e with
    | (Econst ast_num n) => ast_num
    | (Evar ast_num x) => ast_num
    | (Ebinop ast_num op e1 e2) => ast_num
    | (Eunop ast_num op e) => ast_num
    end.

(** get the ast number from the statemet ast node *)
Definition get_ast_num_stmt (c: stmt): astnum :=
    match c with
    | (Sassign ast_num x e) => ast_num
    | (Sseq ast_num c1 c2) => ast_num
    | (Sifthen ast_num b c) => ast_num
    | (Swhile ast_num b c) => ast_num
    end.

Definition max_num := astnum.

(** ast_num for each AST node is unique *)
(** later the ast id will be used to map ast node to the check flag denoting the run-time checks
     that needs to be performed before executing that ast node;
*)

(** all the ast ids for expression ast nodes are unique: parent node's ast id number is smaller than
     children node's ast id number, and the left child node's id number is smaller than the right child 
     node's id number; max_num is the maximum ast id number used in the expression
*)
Inductive ast_num_inc_expr: expr -> max_num -> Prop :=
    | Inc_Econst: forall ast_num n,
        ast_num_inc_expr (Econst ast_num n) ast_num
    | Inc_Evar: forall ast_num x,
        ast_num_inc_expr (Evar ast_num x) ast_num
    | Inc_Ebinop: forall e1 max1 e2 max2 ast_num1 ast_num2 ast_num op,
        ast_num_inc_expr e1 max1 ->
        ast_num_inc_expr e2 max2 ->
        get_ast_num_expr e1 = ast_num1 ->
        get_ast_num_expr e2 = ast_num2 ->
        ast_num < ast_num1 ->
        ast_num < ast_num2 ->
        max1 < ast_num2 ->
        ast_num_inc_expr (Ebinop ast_num op e1 e2) max2
    | Inc_Eunop: forall e max ast_num0 ast_num op,
        ast_num_inc_expr e max ->
        get_ast_num_expr e = ast_num0 ->
        ast_num < ast_num0 ->
        ast_num_inc_expr (Eunop ast_num op e) max.

(** it's similar to ast_num_inc_expr, all ast id number is unique *)
Inductive ast_num_inc_stmt: stmt -> max_num -> Prop :=
    | Inc_Sassign: forall e max ast_num0 ast_num x,
        ast_num_inc_expr e max ->
        get_ast_num_expr e = ast_num0 ->
        ast_num < ast_num0 ->
        ast_num_inc_stmt (Sassign ast_num x e) max
    | Inc_Sseq: forall c1 max1 c2 max2 ast_num1 ast_num2 ast_num,
        ast_num_inc_stmt c1 max1 ->
        ast_num_inc_stmt c2 max2 ->
        get_ast_num_stmt c1 = ast_num1 ->
        get_ast_num_stmt c2 = ast_num2 ->
        ast_num < ast_num1 ->
        ast_num < ast_num2 ->
        max1 < ast_num2 ->
        ast_num_inc_stmt (Sseq ast_num c1 c2) max2
    | Inc_Sifthen: forall b max1 c max2 ast_num1 ast_num2 ast_num,
        ast_num_inc_expr b max1 ->
        ast_num_inc_stmt c max2 ->
        get_ast_num_expr b = ast_num1 ->
        get_ast_num_stmt c = ast_num2 ->
        ast_num < ast_num1 ->
        ast_num < ast_num2 ->
        max1 < ast_num2 ->
        ast_num_inc_stmt (Sifthen ast_num b c) max2
    | Inc_Swhile: forall b max1 c max2 ast_num1 ast_num2 ast_num,
        ast_num_inc_expr b max1 ->
        ast_num_inc_stmt c max2 ->
        get_ast_num_expr b = ast_num1 ->
        get_ast_num_stmt c = ast_num2 ->
        ast_num < ast_num1 -> 
        ast_num < ast_num2 -> 
        max1 < ast_num2 ->
        ast_num_inc_stmt (Swhile ast_num b c) max2.


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
Inductive ast_nums_lt: check_points -> astnum -> Prop := 
    | lt1: forall ls n ast_num ck,
        ast_nums_lt ls n ->
        ast_num < n ->
        ast_nums_lt ((ast_num, ck) ::ls) n
    | lt2: forall n,
        ast_nums_lt nil n.

Lemma ast_nums_lt_trans0: forall ls n n',
    ast_nums_lt ls n ->
    n <= n' ->
    ast_nums_lt ls n'.
Proof.
    intros ls n n' h1 h2.
    induction h1.
  - constructor.
    apply IHh1; assumption.
    intuition.
  - constructor.    
Qed.

Lemma ast_nums_lt_trans: forall ls n n',
    ast_nums_lt ls n ->
    n < n' ->
    ast_nums_lt ls n'.
Proof.
    intros.
    eapply ast_nums_lt_trans0.
    apply H. 
    intuition.
Qed.

Lemma ast_nums_lt_add: forall ast_num n cks flag,
    ast_num < n ->
    ast_nums_lt cks n ->
    ast_nums_lt ((ast_num, flag) :: cks) n.
Proof.
    intros.
    constructor; auto.
Qed.


(** *** generate run-time-check flags for expressions *)
(** compute check flags for each expression ast node according to the checking rules, and the results  
     are stored in a list of type check_points
*)
Inductive check_generator_expr: check_points -> expr -> check_points -> Prop :=
    | CG_Econst: forall ast_num n ls,
        check_generator_expr ls (Econst ast_num n) ls
    | CG_Evar: forall ast_num x ls,
        check_generator_expr ls (Evar ast_num x) ls
    | CG_Ebinop: forall ls e1 ls1 e2 ls2 ast_num op flag,
        check_flag (Ebinop ast_num op e1 e2) (Some flag) -> 
        check_generator_expr ((ast_num, flag) :: ls) e1 ls1 ->
        check_generator_expr ls1 e2 ls2 ->
        check_generator_expr ls (Ebinop ast_num op e1 e2) ls2
    | CG_Ebinop_None: forall ls e1 ls1 e2 ls2 ast_num op,
        check_flag (Ebinop ast_num op e1 e2) None -> 
        check_generator_expr ls e1 ls1 ->
        check_generator_expr ls1 e2 ls2 ->
        check_generator_expr ls (Ebinop ast_num op e1 e2) ls2
    | CG_Eunop: forall ls e ls1 ast_num op,
        check_generator_expr ls e ls1 ->
        check_generator_expr ls (Eunop ast_num op e) ls1.

(** *** generate run-time-check flags for statements *)
(** For the SPARK 2014 subset that we are working on, we only consider the division by zero check and 
     overflow check. So here, the check for each statement is none, but it is extensible to includes necessary 
     checks in the statements in the future. 
 *)
Inductive check_generator_stmt: check_points -> stmt -> check_points -> Prop :=
    | CG_Sassign: forall ls1 e ls2 ast_num x,
        check_generator_expr ls1 e ls2 ->
        check_generator_stmt ls1 (Sassign ast_num x e) ls2
    | CG_Sseq: forall ls1 c1 ls2 c2 ls3 ast_num,
        check_generator_stmt ls1 c1 ls2 ->
        check_generator_stmt ls2 c2 ls3 ->
        check_generator_stmt ls1 (Sseq ast_num c1 c2) ls3
    | CG_Sifthen: forall ls1 b ls2 c ls3 ast_num,
        check_generator_expr ls1 b ls2 ->
        check_generator_stmt ls2 c ls3 ->
        check_generator_stmt ls1 (Sifthen ast_num b c) ls3
    | CG_Swhile: forall ls1 b ls2 c ls3 ast_num,
        check_generator_expr ls1 b ls2 ->
        check_generator_stmt ls2 c ls3 ->        
        check_generator_stmt ls1 (Swhile ast_num b c) ls3.

(** ** Semantics with run-time-checks *)
(*
Inductive correct_flag_on_op: check_action -> binary_operation -> Prop :=
    | Div_Flag: correct_flag_on_op Do_Division_Check Odiv. 
*)

(** the semantics for expressions evaluation, where cps is passed in as a parameter telling 
     whether a check is needed to be performed before executing the expression ast node
*)
Inductive eval_expr_with_checks (cps: check_points): stack -> expr -> return_val -> Prop :=
    | eval_Const: forall cst v s ast_num,
        eval_constant cst = v ->
        eval_expr_with_checks cps s (Econst ast_num cst) (ValNormal v)
    | eval_Var: forall x s v ast_num,
        fetch x s = Some v ->
        eval_expr_with_checks cps s (Evar ast_num x) (ValNormal v)
    | eval_Binop1: forall s e1 ast_num op e2,
        eval_expr_with_checks cps s e1 ValException ->
        eval_expr_with_checks cps s (Ebinop ast_num op e1 e2) ValException
    | eval_Binop2: forall s e1 v1 e2 ast_num op,
        eval_expr_with_checks cps s e1 (ValNormal v1) ->
        eval_expr_with_checks cps s e2 ValException ->
        eval_expr_with_checks cps s (Ebinop ast_num op e1 e2) ValException
    | eval_Binop3: forall s e1 v1 e2 v2 ck ast_num op,
        eval_expr_with_checks cps s e1 (ValNormal v1) ->
        eval_expr_with_checks cps s e2 (ValNormal v2) ->
        fetch_ck ast_num cps = Some ck ->
        do_check op v1 v2 false ->
        eval_expr_with_checks cps s (Ebinop ast_num op e1 e2) ValException
    | eval_Binop4: forall s e1 v1 e2 v2 ck ast_num op v,
        eval_expr_with_checks cps s e1 (ValNormal v1) ->
        eval_expr_with_checks cps s e2 (ValNormal v2) ->
        fetch_ck ast_num cps = Some ck -> 
        do_check op v1 v2 true ->
        eval_binexpr op v1 v2 v ->
        eval_expr_with_checks cps s (Ebinop ast_num op e1 e2) (ValNormal v)
    | eval_Binop5: forall s e1 v1 e2 v2 ast_num op v,
        eval_expr_with_checks cps s e1 (ValNormal v1) ->
        eval_expr_with_checks cps s e2 (ValNormal v2) ->
        fetch_ck ast_num cps = None ->
        eval_binexpr op v1 v2 v ->
        eval_expr_with_checks cps s (Ebinop ast_num op e1 e2) (ValNormal v)
    | eval_Unop1: forall s e ast_num op,
        eval_expr_with_checks cps s e ValException ->
        eval_expr_with_checks cps s (Eunop ast_num op e) ValException
    | eval_Unop2: forall s e v ast_num op v1,
        eval_expr_with_checks cps s e (ValNormal v) ->
        eval_unaryexpr op v v1 ->
        eval_expr_with_checks cps s (Eunop ast_num op e) (ValNormal v1).


(** 
    it's similar to the eval_expr_with_checks: cps is used to denote whether a check is needed to be
    performed before executing the statement; right now, we only consider the division and overflow checks
    for expressions, and there are checks enfornced on the statements
*)
Inductive eval_stmt_with_checks (cps: check_points): stack -> stmt -> state -> Prop :=
    | eval_Assign1: forall s e ast_num x,
        eval_expr_with_checks cps s e ValException ->
        eval_stmt_with_checks cps s (Sassign ast_num x e) SException
    | eval_Assign2: forall s e v x s1 ast_num,
        eval_expr_with_checks cps s e (ValNormal v) ->
        update s x (Value v) = Some s1 -> 
        eval_stmt_with_checks cps s (Sassign ast_num x e) (SNormal s1)
    | eval_Seq1: forall s c1 ast_num c2,
        eval_stmt_with_checks cps s c1 SException ->
        eval_stmt_with_checks cps s (Sseq ast_num c1 c2) SException
    | eval_Seq2: forall ast_num s s1 s2 c1 c2,
        eval_stmt_with_checks cps s c1 (SNormal s1) ->
        eval_stmt_with_checks cps s1 c2 s2 ->
        eval_stmt_with_checks cps s (Sseq ast_num c1 c2) s2
    | eval_Ifthen: forall s b ast_num c,
        eval_expr_with_checks cps s b ValException ->
        eval_stmt_with_checks cps s (Sifthen ast_num b c) SException
    | eval_Ifthen_True: forall s b c s1 ast_num,
        eval_expr_with_checks cps s b (ValNormal (Bool true)) ->
        eval_stmt_with_checks cps s c s1 ->
        eval_stmt_with_checks cps s (Sifthen ast_num b c) s1
    | eval_Ifthen_False: forall s b ast_num c,
        eval_expr_with_checks cps s b (ValNormal (Bool false)) ->
        eval_stmt_with_checks cps s (Sifthen ast_num b c) (SNormal s)
    | eval_While: forall s b ast_num c,
        eval_expr_with_checks cps s b ValException ->
        eval_stmt_with_checks cps s (Swhile ast_num b c) SException
    | eval_While_True1: forall s b c ast_num,
        eval_expr_with_checks cps s b (ValNormal (Bool true)) ->
        eval_stmt_with_checks cps s c SException ->
        eval_stmt_with_checks cps s (Swhile ast_num b c) SException
    | eval_While_True2: forall s b c s1 ast_num s2,
        eval_expr_with_checks cps s b (ValNormal (Bool true)) ->
        eval_stmt_with_checks cps s c (SNormal s1) ->
        eval_stmt_with_checks cps s1 (Swhile ast_num b c) s2 ->
        eval_stmt_with_checks cps s (Swhile ast_num b c) s2
    | eval_While_False: forall s b ast_num c,
        eval_expr_with_checks cps s b (ValNormal (Bool false)) ->
        eval_stmt_with_checks cps s (Swhile ast_num b c) (SNormal s).


(** some basic lemmas *)
(** eval_stmt_with_checks returns either a normal value or an exception when the check is false *)
Lemma eval_expr_with_checks_state: forall ls s e v,
    eval_expr_with_checks ls s e v ->
    (exists v0, v = ValNormal v0) \/ v = ValException.
Proof.
    intros.
    induction H;
    try match goal with
    | [ |- (exists v0 : value, ValNormal ?v = ValNormal v0) \/ _ ] => left; exists v; reflexivity
    | [ |- _ \/ ?A = ?A ] => right; reflexivity
    end.
Qed.

(** 
   the ast id number is increasing: parent node's ast id number is smaller than children node's ast id number.
   (get_ast_num_expr e) is the ast id number for expression e, and max is the maximum ast id number used 
   by e. if e has no subexpression, then max is the same as (get_ast_num_expr e), otherwise, max is maximum
   ast id number of its subexpressions, so (get_ast_num_expr e) should be less and equal max
*)
Lemma ast_num_bound_expr: forall e max,
    ast_num_inc_expr e max ->
    get_ast_num_expr e <= max.
Proof.
    intros e max h.
    induction h; simpl; intuition.
Qed.

(** 
    checks are computed according to the checking rules for expression e and its subexpressions,
    the results are stored in cks indexed by expression and its subexpression ast ids,
    because max is the maximum ast id, so all ast ids in cks should be less than (max + 1)
*)
Lemma ast_num_max_expr: forall e max cks0 cks,
    ast_num_inc_expr e max ->
    check_generator_expr cks0 e cks ->
    ast_nums_lt cks0 (get_ast_num_expr e) ->
    ast_nums_lt cks (max + 1).
Proof.
    intros e max cks0 cks h1.
    revert cks0 cks.
    induction h1;
    intros cks0 cks h2 h3;
    simpl in h3; inversion h2; subst.
  - apply ast_nums_lt_trans with (n := ast_num); intuition.
  - apply ast_nums_lt_trans with (n := ast_num); intuition.
  - specialize (ast_nums_lt_trans _ _ _ h3 H1); intros hz1.
    specialize (ast_nums_lt_add _ _ _ flag H1 hz1); intros hz2.
    specialize (IHh1_1 _ _ H11 hz2).
    assert(hz: max1 + 1 <= get_ast_num_expr e2); intuition.
    specialize (ast_nums_lt_trans0 _ _ _ IHh1_1 hz); intros hz3.
    specialize (IHh1_2 _ _ H12 hz3).
    assumption.
  - specialize (ast_nums_lt_trans _ _ _ h3 H1); intros hz1.
    specialize (IHh1_1 _ _ H11 hz1).
    assert(hz: max1 + 1 <= get_ast_num_expr e2); intuition.
    specialize (ast_nums_lt_trans0 _ _ _ IHh1_1 hz); intros hz3.
    specialize (IHh1_2 _ _ H12 hz3).
    assumption.
  - specialize (ast_nums_lt_trans _ _ _ h3 H0); intros hz1.
    specialize (IHh1 _ _ H5 hz1).
    assumption.
Qed.

(** it's similar to ast_num_bound_expr *)
Lemma ast_num_bound_stmt: forall c max,
    ast_num_inc_stmt c max ->
    get_ast_num_stmt c <= max.
Proof.
    intros c max h.
    induction h; simpl; intuition.
    specialize (ast_num_bound_expr _ _ H); intros hz1.
    intuition.    
Qed.

(** it's similar to ast_num_max_expr *)
Lemma ast_num_max_stmt: forall c max cks0 cks1,
    ast_num_inc_stmt c max ->
    check_generator_stmt cks0 c cks1 ->
    ast_nums_lt cks0 (get_ast_num_stmt c) ->
    ast_nums_lt cks1 (max + 1).
Proof.
    intros c max cks0 cks1 h1.
    revert cks0 cks1.
    induction h1;
    intros cks0 cks1 h2 h3;
    simpl in h3; inversion h2; subst.
  - specialize (ast_nums_lt_trans _ _ _ h3 H1); intros hz1.
    specialize (ast_num_max_expr _ _ _ _ H H7 hz1); intros hz2.
    assumption.
  - specialize (ast_nums_lt_trans _ _ _ h3 H1); intros hz1.
    specialize (IHh1_1 _ _ H9 hz1).
    assert (hz: max1 + 1 <= get_ast_num_stmt c2); intuition.
    specialize (ast_nums_lt_trans0 _ _ _ IHh1_1 hz); intros hz2.
    specialize (IHh1_2 _ _ H10 hz2).
    assumption.
  - specialize (ast_nums_lt_trans _ _ _ h3 H2); intros hz1.
    specialize (ast_num_max_expr _ _ _ _ H H10 hz1); intros hz2.
    assert (hz: max1 + 1 <= get_ast_num_stmt c); intuition.
    specialize (ast_nums_lt_trans0 _ _ _ hz2 hz); intros hz3.
    specialize (IHh1 _ _ H11 hz3).
    assumption.
  - specialize (ast_nums_lt_trans _ _ _ h3 H2); intros hz1.
    specialize (ast_num_max_expr _ _ _ _ H H10 hz1); intros hz2.
    assert (hz: max1 + 1 <= get_ast_num_stmt c); intuition.
    specialize (ast_nums_lt_trans0 _ _ _ hz2 hz); intros hz3.
    specialize (IHh1 _ _ H11 hz3).
    assumption.
Qed.














