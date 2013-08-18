Require Export environment.
Require Export semantics.

(** * Well-Formed Program  *)
(**
   Before executing the program, make sure that the program is well-formed
   - well-typed
      - unary/binary operators have right type of operands;
      - types on both sides of assignments are consistent;
      - used variables has right _in/out_ mode;
   - well-defined 
      - all used variables are initialized
   - well-checked
      - right checks are put at the right places according to the checking rules
*)

(** this is used by the type system to check whether types are consistent 
    on both sides of binary operators, and return either the result type or 
    None if their types are not consistent;
*)
Definition binop_type (op: binary_operator) (t1 t2: type): option type := 
    match op with
    | Equal | Not_Equal | Greater_Than | Greater_Than_Or_Equal 
    | Less_Than | Less_Than_Or_Equal  => 
        match t1, t2 with
        | Integer, Integer => Some Boolean
        | _, _ => None
        end
    | And | Or =>
        match t1, t2 with
        | Boolean, Boolean => Some Boolean
        | _, _ => None
        end
    | Plus | Minus | Multiply | Divide =>
        match t1, t2 with
        | Integer, Integer => Some Integer
        | _, _ => None
        end
    end.

Definition unop_type (op: unary_operator) (t: type): option type := 
    match op with 
    | Not => match t with
             | Boolean => Some Boolean
             | _ => None
             end
    end.

(** * Well-Typed *)
(** ** Well-typed expressions *)
(**
   - type check for expressions;
*)
Inductive well_typed_expr: symtb -> expression -> type -> Prop :=
    | WT_Literal_Int: forall ast_num n tb,
        well_typed_expr tb (E_Literal ast_num (Integer_Literal n)) Integer
    | WT_Literal_Bool: forall ast_num b tb,
        well_typed_expr tb (E_Literal ast_num (Boolean_Literal b)) Boolean
    | WT_Identifier: forall ast_num x tb m t,
        lookup x tb = Some (m, t) ->  
        well_typed_expr tb (E_Identifier ast_num x) t
    | WT_Binary_Operation: forall ast_num tb op e1 e2 t t1,
        well_typed_expr tb e1 t ->
        well_typed_expr tb e2 t ->
        binop_type op t t = Some t1 ->
        well_typed_expr tb (E_Binary_Operation ast_num op e1 e2) t1
    | WT_Unary_Operation: forall ast_num tb op e,
        well_typed_expr tb e Boolean ->
        well_typed_expr tb (E_Unary_Operation ast_num op e) Boolean.

(** ** Well-typed statements *)
(**
    - type check for statements;
*)
Inductive well_typed_stmt: symtb -> statement  -> Prop :=
    | WT_Assignment: forall ast_num tb x e m t,
        lookup x tb = Some (m, t) ->
        well_typed_expr tb e t ->
        well_typed_stmt tb ((S_Assignment ast_num x e))
    | WT_Sequence: forall ast_num c1 c2 tb,
        well_typed_stmt tb c1 ->
        well_typed_stmt tb c2 ->
        well_typed_stmt tb (S_Sequence ast_num c1 c2)
    | WT_If: forall ast_num tb b c,
        well_typed_expr tb b Boolean ->
        well_typed_stmt tb c ->
        well_typed_stmt tb (S_If ast_num b c)
    | WT_While_Loop: forall ast_num tb b c,
        well_typed_expr tb b Boolean ->
        well_typed_stmt tb c ->
        well_typed_stmt tb (S_While_Loop ast_num b c).


(* in our formalization framework, all names used in the SPARK programs 
   are formalized as integer numbers, for example, variables, 
   function/procedure names and types are all represented as 
   unique integer numbers; here I hard code that number "1" 
   representing type "Integer", and "2" representing "Boolean";
*)
Inductive type_map: typenum -> type -> Prop :=
    | T1: type_map 1 Integer
    | T2: type_map 2 Boolean.

(** type check for varialbe declaration; *)
Inductive well_typed_decl: symtb -> object_declaration -> symtb -> Prop :=
    | WT_Decl0: forall d x t tb,
        x = d.(object_name) ->
        type_map d.(object_nominal_subtype) t ->
        None = d.(initialization_expression) ->
        well_typed_decl tb d ((x, (In_Out, t)) :: tb) (* the declared variables have in/out mode *)
    | WT_Decl1: forall d x t i tb,
        x = d.(object_name) ->
        type_map d.(object_nominal_subtype) t ->
        Some i = d.(initialization_expression) -> 
        well_typed_expr tb i t -> (* the type of the initialization value should be consistent with the declared variable's type *)
        well_typed_decl tb d ((x, (In_Out, t)) :: tb).

Inductive well_typed_decls: symtb -> list object_declaration -> symtb -> Prop :=
    | WT_Decls_Empty: forall tb,
        well_typed_decls tb nil tb
    | WT_Decls: forall tb d tb'0 tl tb',
        well_typed_decl tb d tb'0 ->
        well_typed_decls tb'0 tl tb' ->
        well_typed_decls tb (d :: tl) tb'.

(** type check for procedure body; *)
Inductive well_typed_proc_body: symtb -> procedure_body -> Prop :=
    | WT_Proc_Body: forall tb f tb',
        well_typed_decls tb f.(procedure_declarative_part) tb' ->
        well_typed_stmt tb' f.(procedure_statements) ->
        well_typed_proc_body tb f.

(** type check for subproram, which can be either procedure or function; *)
Inductive well_typed_subprogram: symtb -> subprogram -> Prop :=
    | WT_Procedure: forall tb f ast_num,
        well_typed_proc_body tb f ->
        well_typed_subprogram tb (Procedure ast_num f).

(* =============================== *)

(** functional semantics for type system *)

(** type check expression; *)
Function f_well_typed_expr (tb: symtb) (e: expression): option type := 
    match e with
    | E_Literal _ (Integer_Literal n) => Some Integer
    | E_Literal _ (Boolean_Literal n) => Some Boolean
    | E_Identifier _ x =>
        match (lookup x tb) with
        | Some (m, t) => Some t
        | None => None
        end
    | E_Binary_Operation _ op e1 e2 =>
        match (f_well_typed_expr tb e1) with
        | Some t1 => 
            match (f_well_typed_expr tb e2) with
            | Some t2 => binop_type op t1 t2
            | None => None
            end
        | None => None
        end   
    | E_Unary_Operation _ op e => 
        match f_well_typed_expr tb e with
        | Some t => unop_type op t
        | None => None
        end
    end.

Function f_typ_equal (t1: type) (t2: type): bool :=
    match t1, t2 with
    | Integer, Integer => true
    | Boolean, Boolean => true
    | _, _ => false
    end.

(** type check statement; *)
Function f_well_typed_stmt (tb: symtb) (c: statement): bool :=
    match c with
    | S_Assignment ast_num x e =>
        match (f_well_typed_expr tb e) with
        | Some t1 => 
            match lookup x tb with
            | Some (m, t2) => (f_typ_equal t1 t2)
            | None => false
            end
        | None => false
        end
    | S_Sequence ast_num c1 c2 =>
        match f_well_typed_stmt tb c1 with
        | true => f_well_typed_stmt tb c2
        | false => false
        end
    | S_If ast_num b c =>
        match f_well_typed_expr tb b with
        | Some Boolean => f_well_typed_stmt tb c
        | _ => false
        end
    | S_While_Loop ast_num b c =>
        match f_well_typed_expr tb b with
        | Some Boolean => f_well_typed_stmt tb c
        | _ => false
        end
    end.


(** in the SPARK formalization, natural number are used to represent 
    identifier, type and so on, here "1" represents type Integer, 
    and "2" represents type Boolean;
*)
Function f_type_map (n: typenum): option type :=
    match n with
    | 1 => Some Integer
    | 2 => Some Boolean
    | _ => None
    end.

(** type check variable declaration; *)
Function f_well_typed_decl (tb: symtb) (d: object_declaration): option symtb :=
    match f_type_map d.(object_nominal_subtype) with
    | Some t =>
        match d.(initialization_expression) with
        | Some i => 
            match f_well_typed_expr tb i with
            | Some t' => if f_typ_equal t t' then Some ((d.(object_name), (In_Out, t)) :: tb) else None
            | None => None
            end
        | None => Some ((d.(object_name), (In_Out, t)) :: tb)
        end
    | None => None
    end.

Function f_well_typed_decls (tb: symtb) (ds: list object_declaration): option symtb :=
    match ds with
    | d :: tl => 
        match f_well_typed_decl tb d with
        | Some tb' => f_well_typed_decls tb' tl
        | None => None
        end
    | nil => Some tb
    end.

(** type check procedure body; *)
Function f_well_typed_proc_body (tb: symtb) (f: procedure_body): bool :=
    match f_well_typed_decls tb f.(procedure_declarative_part) with
    | Some tb' => f_well_typed_stmt tb' f.(procedure_statements)
    | None => false
    end.

(** type check subprogram, which can be either procedure or function; *)
Function f_well_typed_subprogram (tb: symtb) (p: subprogram): bool :=
    match p with
    | Procedure ast_num f => f_well_typed_proc_body tb f
    end.

(* =============================== *)

(** Semantical equivalence between relational and functional 
    semantics for type system; 
*)

(** bisimulation between f_well_typed_expr and well_typed_expr 
    for expression; 
*)
Lemma f_well_typed_expr_correct: forall tb e t,
    f_well_typed_expr tb e = Some t ->
    well_typed_expr tb e t.
Proof.
    intros tb e.
    functional induction (f_well_typed_expr tb e);
    intros t'0 h1;
    inversion h1; subst;
    try constructor.
  - econstructor.
    apply e1.
  - specialize (IHo _ e3).
    specialize (IHo0 _ e4).
    econstructor.
    apply IHo.
    destruct t1, t2, op; 
    inversion h1; auto.
    destruct t1, t2, op;
    inversion h1; auto.
  - specialize (IHo _ e2).
    destruct t, t'0, op; inversion h1.
    constructor.
    assumption.
Qed.

Lemma f_well_typed_expr_complete: forall tb e t,
    well_typed_expr tb e t ->
    f_well_typed_expr tb e = Some t.
Proof.
    intros tb e t h1.
    induction h1;
    try constructor;
    simpl.
  - rewrite H. reflexivity.
  - rewrite IHh1_1, IHh1_2.
    assumption.
  - rewrite IHh1.
    destruct op; auto.
Qed.

(** bisimulation between f_well_typed_stmt and well_typed_stmt for statement *)
Lemma f_well_typed_stmt_correct: forall tb c,
    f_well_typed_stmt tb c = true ->
    well_typed_stmt tb c.
Proof.
    intros tb c.
    functional induction (f_well_typed_stmt tb c);
    intros h1;
    try match goal with
    | [h: false = true |- _] => inversion h
    end.
  - econstructor.
    apply e2.
    specialize (f_well_typed_expr_correct _ _ _ e1); intros h2.
    destruct t1, t2; inversion h1;
    auto.
  - specialize (IHb e0).
    specialize (IHb0 h1).
    constructor; assumption.
  - specialize (IHb h1).
    constructor; auto.
    specialize (f_well_typed_expr_correct _ _ _ e0); intros h2.
    assumption.
  - specialize (IHb h1).
    constructor; auto.
    specialize (f_well_typed_expr_correct _ _ _ e0); intros h2.
    assumption.
Qed.

Lemma f_well_typed_stmt_complete: forall tb c,
    well_typed_stmt tb c ->
    f_well_typed_stmt tb c = true.
Proof.
    intros tb c h1.
    induction h1; simpl.
  - specialize (f_well_typed_expr_complete _ _ _ H0); intros h2.
    rewrite h2.
    rewrite H.
    destruct t; auto.
  - rewrite IHh1_1, IHh1_2.
    reflexivity.
  - specialize (f_well_typed_expr_complete _ _ _ H); intros h2.
    rewrite h2, IHh1.
    reflexivity.
  - specialize (f_well_typed_expr_complete _ _ _ H); intros h2.
    rewrite h2, IHh1.
    reflexivity.
Qed.

Lemma type_map_equal: forall n t,
    f_type_map n = Some t <-> type_map n t.
Proof.
    intros n t; split;
    intros h1.
  - functional induction (f_type_map n);
    inversion h1; subst;
    constructor.
  - induction h1;
    simpl; auto.
Qed.

(** bisimulation between f_well_typed_decl and well_typed_decl for 
    variable declaration; 
*)
Lemma f_well_typed_decl_correct: forall tb d tb',
    f_well_typed_decl tb d = Some tb' ->
    well_typed_decl tb d tb'.
Proof.
    intros tb d.
    functional induction f_well_typed_decl tb d;
    intros tb' h1;
    inversion h1; subst.
  - eapply WT_Decl1; auto.
    + apply type_map_equal; 
      assumption.
    + symmetry in e0; apply e0.
    + specialize (f_well_typed_expr_correct _ _ _ e1); intros h2.
      destruct t, t'; inversion e2; auto.
  - eapply WT_Decl0; auto.
    apply type_map_equal; assumption.
Qed.

Lemma f_well_typed_decl_complete: forall tb d tb',
    well_typed_decl tb d tb' ->
    f_well_typed_decl tb d = Some tb'.
Proof.
    intros tb d tb' h1.
    induction h1;
    specialize (type_map_equal (object_nominal_subtype d) t); intros h2;
    destruct h2 as [h3 h4];
    specialize (h4 H0);
    unfold f_well_typed_decl;
    rewrite h4; rewrite <- H1; rewrite <- H.
  - reflexivity.
  - specialize (f_well_typed_expr_complete _ _ _ H2); intros h2.
    rewrite h2.
    destruct t; simpl; auto.
Qed.

(** bisimulation between f_well_typed_decls and well_typed_decls for
    list of variable declarations;
*)
Lemma f_well_typed_decls_correct: forall tb ds tb',
    f_well_typed_decls tb ds = Some tb' ->
    well_typed_decls tb ds tb'.
Proof.
    intros tb ds.
    functional induction (f_well_typed_decls tb ds);
    intros tb'0 h1.
  - specialize (IHo _ h1).
    econstructor.
    specialize (f_well_typed_decl_correct _ _ _ e0); intros h2.
    apply h2.
    assumption.
  - inversion h1.
  - inversion h1; subst.
    constructor.
Qed.

Lemma f_well_typed_decls_complete: forall tb ds tb',
    well_typed_decls tb ds tb' ->
    f_well_typed_decls tb ds = Some tb'.
Proof.
    intros tb ds tb' h1.
    induction h1.
  - simpl; auto.
  - specialize (f_well_typed_decl_complete _ _ _ H); intros h2.
    simpl.
    rewrite h2. assumption.
Qed.


(** bisimulation between f_well_typed_proc_body and well_typed_proc_body for 
    procedure body
*)
Lemma f_well_typed_proc_body_correct: forall tb f,
    f_well_typed_proc_body tb f = true ->
    well_typed_proc_body tb f.
Proof.
    intros tb f h1.
    functional induction (f_well_typed_proc_body tb f).
  - econstructor.
    specialize (f_well_typed_decls_correct _ _ _ e); intros h2.
    apply h2.
    specialize (f_well_typed_stmt_correct _ _ h1); intros h2.
    assumption.
  - inversion h1.
Qed.

Lemma f_well_typed_proc_body_complete: forall tb f,
    well_typed_proc_body tb f ->
    f_well_typed_proc_body tb f = true.
Proof.
    intros tb f h1.
    induction h1.
    specialize (f_well_typed_decls_complete _ _ _ H); intros h1.
    specialize (f_well_typed_stmt_complete _ _ H0); intros h2.
    unfold f_well_typed_proc_body.
    rewrite h1, h2.
    auto.
Qed.


(** bisimulation between f_well_typed_subprogram and 
    well_typed_subprogram for subprogram; 
*)
Lemma f_well_typed_subprogram_correct: forall tb p,
    f_well_typed_subprogram tb p = true ->
    well_typed_subprogram tb p.
Proof.
    intros tb p h1.
    functional induction (f_well_typed_subprogram tb p).
    specialize (f_well_typed_proc_body_correct _ _ h1); intros h2.
    constructor.
    assumption.
Qed.

Lemma f_well_typed_subprogram_complete: forall tb p,
    well_typed_subprogram tb p ->
    f_well_typed_subprogram tb p = true.
Proof.
    intros tb p h1.
    induction h1.
    specialize (f_well_typed_proc_body_complete _ _ H); intros h1.
    simpl. assumption.
Qed.


(* =============================== *)

(** * Well-Defined *)

(** Well-Defined means that all referenced variables are initialized *)
(** the initialization modes can be either Init (initialized) or 
    Uninit (uninitialized); 
*)
Inductive init_mode: Type := 
    | Init: init_mode
    | Uninit: init_mode.

(** map from variable to its initialization state and in/out mode *)
Definition mode_map: Type := list (idnum * (init_mode * mode)).

(** basic functions for fetching and updating the variable's 
    initialization state; 
*)
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
   - all variables used in expression should be either in mode 
     _in_ or _in/out_; 
*)
Inductive well_defined_expr: mode_map -> expression -> Prop :=
    | WD_Literal_Int: forall ast_num m n,
        well_defined_expr m (E_Literal ast_num (Integer_Literal n))
    | WD_Literal_Bool: forall ast_num m b,
        well_defined_expr m (E_Literal ast_num (Boolean_Literal b))
    | WD_Identifier: forall ast_num x m md,
        fetch2 x m = Some (Init, md) -> (* initialized out variables can also be read *)
        well_defined_expr m (E_Identifier ast_num x)
    | WD_Binary_Operation: forall ast_num m op e1 e2,
        well_defined_expr m e1 ->
        well_defined_expr m e2 ->
        well_defined_expr m (E_Binary_Operation ast_num op e1 e2)
    | WD_Unary_Operation: forall ast_num m op e,
        well_defined_expr m e ->
        well_defined_expr m (E_Unary_Operation ast_num op e). 


(** ** Well-defined statements *)
(** 
    update by assignment will make the uninitialized variables into 
    initialized one, so in the following definition, we have to track 
    the initialization states after executing each statement, and use 
    the latest initialization state to check whether the used variables 
    are initialized or not;
    For conditional and while loop commands, their final initialization 
    state are the intersection of the resulting initialization states 
    from both branches;
    - _in/out_ mode checking (for variables that are updated by 
      assignments, their mode should be either _out_ or _in\out_);
*)

Inductive well_defined_stmt: mode_map -> statement -> mode_map -> Prop :=
    | WD_Assignment: forall m e x i md m' ast_num,
        well_defined_expr m e ->
        fetch2 x m = Some (i, md) ->
        md <> In ->
        update2 m x (Init, md) = Some m' ->
        well_defined_stmt m (S_Assignment ast_num x e) m'
    | WD_Sequence: forall ast_num c1 c2 m m' m'',
        well_defined_stmt m c1 m' ->
        well_defined_stmt m' c2 m'' ->
        well_defined_stmt m (S_Sequence ast_num c1 c2) m''
    | WD_If: forall ast_num m m' b c,
        well_defined_expr m b ->
        well_defined_stmt m c m' ->
        well_defined_stmt m (S_If ast_num b c) m
    | WD_While_Loop: forall ast_num m m' b c,
        well_defined_expr m b ->
        well_defined_stmt m c m' ->
        well_defined_stmt m (S_While_Loop ast_num b c) m.


(** in our current SPARK subset, we only consider Integer and Boolean 
    types, which have no default initialization values, so for any 
    declared variable, if it's declared without initialization 
    expression, then it's uninitialized;
*)
Inductive well_defined_decl: mode_map -> object_declaration -> mode_map -> Prop :=
    | WD_Decl0: forall d x m,
        x = d.(object_name) ->
        None = d.(initialization_expression) ->
        well_defined_decl m d ((x, (Uninit, In_Out)) :: m) 
    | WD_Decl1: forall d x i m,
        x = d.(object_name) ->
        Some i = d.(initialization_expression) ->
        well_defined_expr m i ->
        well_defined_decl m d ((x, (Init, In_Out)) :: m).

Inductive well_defined_decls: mode_map -> list object_declaration -> mode_map -> Prop :=
    | WD_Decls_Empty: forall m,
        well_defined_decls m nil m
    | WD_Decls: forall m d m'0 tl m',
        well_defined_decl m d m'0 ->
        well_defined_decls m'0 tl m' ->
        well_defined_decls m (d :: tl) m'.

Inductive well_defined_proc_body: mode_map -> procedure_body -> mode_map -> Prop :=
    | WD_Proc_Body: forall m f m'0 m',
        well_defined_decls m f.(procedure_declarative_part) m'0 ->
        well_defined_stmt m'0 f.(procedure_statements) m' -> 
        well_defined_proc_body m f m'.

Inductive well_defined_subprogram: mode_map -> subprogram -> mode_map -> Prop :=
    | WD_Procedure: forall m f m' ast_num,
        well_defined_proc_body m f m' ->        
        well_defined_subprogram m (Procedure ast_num f) m'.

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

(** ** Constructing mode map from variable id to a pair of 
    (initialization state * in/out mode) 
*)
(** 
   for any variable in stack, if it has a defined value then it 
   has an initialized state, otherwise, it's uninitialized;
*)
Inductive mode_mapping: symtb -> stack -> (mode_map) -> Prop :=
    | M_Empty: mode_mapping nil nil nil
    | M_Bool: forall tb s x m b ls,
          mode_mapping tb s ls ->
          mode_mapping ((x, (m, Boolean)) :: tb) ((x, (Value (Bool b))) :: s) ((x, (Init, m)) :: ls)
    | M_Int: forall tb s x m v ls,
          mode_mapping tb s ls ->
          mode_mapping ((x, (m, Integer)) :: tb) ((x, (Value (Int v))) :: s) ((x, (Init, m)) :: ls)
    | M_Undefined_Bool: forall tb s x m ls,
          mode_mapping tb s ls ->
          mode_mapping ((x, (m, Boolean)) :: tb) ((x, Undefined) :: s) ((x, (Uninit, m)) :: ls)
    | M_Undefined_Int: forall tb s x m ls,
          mode_mapping tb s ls ->
          mode_mapping ((x, (m, Integer)) :: tb) ((x, Undefined) :: s) ((x, (Uninit, m)) :: ls).

Lemma mode_mapping_unique: forall tb s m1 m2,
    mode_mapping tb s m1 ->
    mode_mapping tb s m2 ->
    m1 = m2.
Proof.
    intros tb s m1 m2 H.
    revert m2.
    induction H;
    intros m2 H0;
    inversion H0; subst;
    auto.
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

(* =============================== *)
Function f_mode_mapping (tb: symtb) (s: stack): option mode_map :=
    match tb, s with
    | nil, nil => Some nil
    | ((x, (md, Boolean)) :: tb'), ((x', (Value (Bool b))) :: s') => 
        if beq_nat x x' then
          match f_mode_mapping tb' s' with
          | Some m => Some ((x, (Init, md)) :: m)
          | None => None
          end
        else 
          None
    | ((x, (md, Integer)) :: tb'), ((x', (Value (Int v))) :: s') => 
        if beq_nat x x' then
          match f_mode_mapping tb' s' with
          | Some m => Some ((x, (Init, md)) :: m)
          | None => None
          end
        else 
          None
    | ((x, (md, Boolean)) :: tb'), ((x', Vundef) :: s') => 
        if beq_nat x x' then
          match f_mode_mapping tb' s' with
          | Some m => Some ((x, (Uninit, md)) :: m)
          | None => None
          end
        else
          None
    | ((x, (md, Integer)) :: tb'), ((x', Vundef) :: s') => 
        if beq_nat x x' then
          match f_mode_mapping tb' s' with
          | Some m => Some ((x, (Uninit, md)) :: m)
          | None => None
          end
        else
          None
    | _, _ => None
    end.


(* =============================== *)

(** Functional semantics for checking whether used variables being 
    initialized
*)
Function f_well_defined_expr (m: mode_map) (e: expression): bool :=
    match e with
    | E_Literal ast_num v => true
    | E_Identifier ast_num x =>
        match fetch2 x m with
        | Some (Init, md) => true
        | _ => false
        end
    | E_Binary_Operation ast_num op e1 e2 =>
        if (f_well_defined_expr m e1) then (f_well_defined_expr m e2) else false
    | E_Unary_Operation ast_num op e => f_well_defined_expr m e
    end.

Function f_well_defined_stmt (m: mode_map) (c: statement): option mode_map :=
    match c with
    | S_Assignment ast_num x e =>
        match fetch2 x m with
        | Some (_, Out) => 
            if f_well_defined_expr m e then update2 m x (Init, Out) else None
        | Some (_, In_Out) => 
            if f_well_defined_expr m e then update2 m x (Init, In_Out) else None
        | _ => None
        end
    | S_Sequence ast_num c1 c2 =>
        match f_well_defined_stmt m c1 with
        | Some m' => f_well_defined_stmt m' c2
        | None => None
        end
    | S_If ast_num b c =>
        if f_well_defined_expr m b 
        then 
            match f_well_defined_stmt m c with
            | Some m' => Some m
            | None => None
            end
        else None
    | S_While_Loop ast_num b c =>
        if f_well_defined_expr m b 
        then 
            match f_well_defined_stmt m c with
            | Some m' => Some m
            | None => None
            end
        else None
    end.

Function f_well_defined_decl (m: mode_map) (d: object_declaration): option mode_map :=
    match d.(initialization_expression) with
    | Some i => 
        if f_well_defined_expr m i then Some ((d.(object_name), (Init, In_Out)) :: m) else None
    | None => Some ((d.(object_name), (Uninit, In_Out)) :: m)
    end.

Function f_well_defined_decls (m: mode_map) (ds: list object_declaration): option mode_map :=
    match ds with
    | d :: tl =>
        match f_well_defined_decl m d with
        | Some m' => f_well_defined_decls m' tl
        | None => None
        end
    | nil => Some m
    end.

Function f_well_defined_proc_body (m: mode_map) (f: procedure_body): option mode_map :=
    match f_well_defined_decls m f.(procedure_declarative_part) with
    | Some m' => f_well_defined_stmt m' f.(procedure_statements)
    | None => None
    end.

Function f_well_defined_subprogram (m: mode_map) (p: subprogram): option mode_map :=
    match p with
    | Procedure ast_num f => f_well_defined_proc_body m f
    end.


(* =============================== *)

(** Semantical equivalence between relational and functional semantics for 
    initialization state checking system;
*)

Lemma f_well_defined_expr_correct: forall m e,
    f_well_defined_expr m e = true ->
    well_defined_expr m e.
Proof.
    intros m e h1.
    functional induction (f_well_defined_expr m e).
  - destruct v; constructor.
  - econstructor.
    apply e1.
  - inversion h1.
  - specialize (IHb e3).
    specialize (IHb0 h1).
    constructor; assumption.
  - inversion h1.
  - specialize (IHb h1).
    constructor; assumption.
Qed.

Lemma f_well_defined_expr_complete: forall m e,
    well_defined_expr m e ->
    f_well_defined_expr m e = true.
Proof.
    intros m e h1.
    induction h1;
    simpl; auto.
  - rewrite H.
    reflexivity.
  - rewrite IHh1_1.
    assumption.
Qed.

Lemma f_well_defined_stmt_correct: forall m c m',
    f_well_defined_stmt m c = Some m' ->
    well_defined_stmt m c m'.
Proof.
    intros m c.
    functional induction (f_well_defined_stmt m c);
    intros m'0 h1;
    try match goal with
    | [h: None = Some ?x |- _] => inversion h
    end.
  - econstructor.
    specialize (f_well_defined_expr_correct _ _ e2); auto.
    apply e1.
    intuition. inversion H.
    assumption.
  - econstructor.
    specialize (f_well_defined_expr_correct _ _ e2); auto.
    apply e1.
    intuition. inversion H.
    assumption.
  - specialize (IHo _ e0).
    specialize (IHo0 _ h1).
    econstructor.
    apply IHo. apply IHo0.
  - inversion h1; subst.
    specialize (IHo _ e1).
    econstructor.
    specialize (f_well_defined_expr_correct _ _ e0); auto.
    apply IHo.
  - inversion h1; subst.
    specialize (IHo _ e1).
    econstructor.
    specialize (f_well_defined_expr_correct _ _ e0); auto.
    apply IHo.
Qed.

Lemma f_well_defined_stmt_complete: forall m c m',
    well_defined_stmt m c m' ->
    f_well_defined_stmt m c = Some m'.
Proof.
    intros m c m' h1.
    induction h1; simpl.
  - rewrite H0.
    specialize (f_well_defined_expr_complete _ _ H); intros hz1.
    rewrite hz1.
    destruct md; auto.
    destruct H1; auto.
  - rewrite IHh1_1, IHh1_2.
    reflexivity.
  - specialize (f_well_defined_expr_complete _ _ H); intros hz1.
    rewrite hz1, IHh1.
    reflexivity.
  - specialize (f_well_defined_expr_complete _ _ H); intros hz1.
    rewrite hz1, IHh1.
    reflexivity.
Qed.

Lemma f_well_defined_decl_correct: forall m d m',
    f_well_defined_decl m d = Some m' ->
    well_defined_decl m d m'.
Proof.
    intros m d.
    functional induction (f_well_defined_decl m d);
    intros m' h1;
    inversion h1; subst.
  - econstructor; auto.
    symmetry in e. apply e.
    specialize (f_well_defined_expr_correct _ _ e0); auto.
  - econstructor; auto.
Qed.

Lemma f_well_defined_decl_complete: forall m d m',
    well_defined_decl m d m' ->
    f_well_defined_decl m d = Some m'.
Proof.
    intros m d m' h1.
    induction h1;
    unfold f_well_defined_decl;
    rewrite <- H0, H.
  - reflexivity.
  - specialize (f_well_defined_expr_complete _ _ H1); intros hz1.
    rewrite hz1.
    reflexivity.
Qed.

Lemma f_well_defined_decls_correct: forall m ds m',
    f_well_defined_decls m ds = Some m' ->
    well_defined_decls m ds m'.
Proof.
    intros m ds.
    functional induction (f_well_defined_decls m ds);
    intros m'0 h1.
  - specialize (IHo _ h1).
    econstructor.
    specialize (f_well_defined_decl_correct _ _ _ e0); intros hz1.
    apply hz1.
    assumption.
  - inversion h1.
  - inversion h1; subst.
    constructor.
Qed.

Lemma f_well_defined_decls_complete: forall m ds m',
    well_defined_decls m ds m' ->
    f_well_defined_decls m ds = Some m'.
Proof.
    intros m ds m' h1.
    induction h1; simpl.
  - reflexivity.
  - specialize (f_well_defined_decl_complete _ _ _ H); intros hz1.
    rewrite hz1.
    rewrite IHh1.
    reflexivity.
Qed.

Lemma f_well_defined_proc_body_correct: forall m f m',
    f_well_defined_proc_body m f = Some m' ->
    well_defined_proc_body m f m'.
Proof.
    intros m f.
    functional induction (f_well_defined_proc_body m f);
    intros m'0 h1.
  - econstructor.
    specialize (f_well_defined_decls_correct _ _ _ e); intro hz1.
    apply hz1.
    specialize (f_well_defined_stmt_correct _ _ _ h1); intros hz2.
    exact hz2.
  - inversion h1.
Qed.

Lemma f_well_defined_proc_body_complete: forall m f m',
    well_defined_proc_body m f m' ->
    f_well_defined_proc_body m f = Some m'.
Proof.
    intros m f m' h1.
    induction h1.
    unfold f_well_defined_proc_body.
    specialize (f_well_defined_decls_complete _ _ _ H); intros hz1.
    specialize (f_well_defined_stmt_complete _ _ _ H0); intros hz2.
    rewrite hz1, hz2.
    reflexivity.
Qed.

Lemma f_well_defined_subprogram_correct: forall m p m',
    f_well_defined_subprogram m p = Some m' ->
    well_defined_subprogram m p m'.
Proof.
    intros m p.
    functional induction (f_well_defined_subprogram m p);
    intros m' h1.
    constructor.
    specialize (f_well_defined_proc_body_correct _ _ _ h1); auto.
Qed.

Lemma f_well_defined_subprogram_complete: forall m p m',
    well_defined_subprogram m p m' ->
    f_well_defined_subprogram m p = Some m'.
Proof.
    intros m p m' h1.
    induction h1.
    simpl.
    specialize (f_well_defined_proc_body_complete _ _ _ H); auto.
Qed.


(* = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = *)

(** * Well-Checked *)
(** get the ast number from the expression ast node *)
Definition get_ast_num_expr (e: expression): astnum :=
    match e with
    | (E_Literal ast_num n) => ast_num
    | (E_Identifier ast_num x) => ast_num
    | (E_Binary_Operation ast_num op e1 e2) => ast_num
    | (E_Unary_Operation ast_num op e) => ast_num
    end.

(** get the ast number from the statemet ast node *)
Definition get_ast_num_stmt (c: statement): astnum :=
    match c with
    | (S_Assignment ast_num x e) => ast_num
    | (S_Sequence ast_num c1 c2) => ast_num
    | (S_If ast_num b c) => ast_num
    | (S_While_Loop ast_num b c) => ast_num
    end.


Definition max_num := astnum.

(** ast_num for each AST node is unique *)
(** later the ast number will be used to map its labled ast node to 
    the check flags denoting the run-time checks that needs to be 
    performed before executing that ast node;
*)

(** all the ast numbers for expression ast nodes are unique: 
    in the ast tree, parent node's ast number is smaller than 
    children node's ast number, and the left child node's ast 
    number is smaller than the right child node's ast number; 
    max_num is the maximum ast number used in the expression;
*)
Inductive ast_num_inc_expr: expression -> max_num -> Prop :=
    | Inc_Literal: forall ast_num n,
        ast_num_inc_expr (E_Literal ast_num n) ast_num
    | Inc_Identifier: forall ast_num x,
        ast_num_inc_expr (E_Identifier ast_num x) ast_num
    | Inc_Binary_Operation: forall e1 max1 e2 max2 ast_num1 ast_num2 ast_num op,
        ast_num_inc_expr e1 max1 ->
        ast_num_inc_expr e2 max2 ->
        get_ast_num_expr e1 = ast_num1 ->
        get_ast_num_expr e2 = ast_num2 ->
        ast_num < ast_num1 ->
        ast_num < ast_num2 ->
        max1 < ast_num2 ->
        ast_num_inc_expr (E_Binary_Operation ast_num op e1 e2) max2
    | Inc_Unary_Operation: forall e max ast_num0 ast_num op,
        ast_num_inc_expr e max ->
        get_ast_num_expr e = ast_num0 ->
        ast_num < ast_num0 ->
        ast_num_inc_expr (E_Unary_Operation ast_num op e) max.

(** it's similar to ast_num_inc_expr, all ast numbers used in the 
    AST tree of statement are unique; 
*)
Inductive ast_num_inc_stmt: statement -> max_num -> Prop :=
    | Inc_Assignment: forall e max ast_num0 ast_num x,
        ast_num_inc_expr e max ->
        get_ast_num_expr e = ast_num0 ->
        ast_num < ast_num0 ->
        ast_num_inc_stmt (S_Assignment ast_num x e) max
    | Inc_Sequence: forall c1 max1 c2 max2 ast_num1 ast_num2 ast_num,
        ast_num_inc_stmt c1 max1 ->
        ast_num_inc_stmt c2 max2 ->
        get_ast_num_stmt c1 = ast_num1 ->
        get_ast_num_stmt c2 = ast_num2 ->
        ast_num < ast_num1 ->
        ast_num < ast_num2 ->
        max1 < ast_num2 ->
        ast_num_inc_stmt (S_Sequence ast_num c1 c2) max2
    | Inc_If: forall b max1 c max2 ast_num1 ast_num2 ast_num,
        ast_num_inc_expr b max1 ->
        ast_num_inc_stmt c max2 ->
        get_ast_num_expr b = ast_num1 ->
        get_ast_num_stmt c = ast_num2 ->
        ast_num < ast_num1 ->
        ast_num < ast_num2 ->
        max1 < ast_num2 ->
        ast_num_inc_stmt (S_If ast_num b c) max2
    | Inc_While_Loop: forall b max1 c max2 ast_num1 ast_num2 ast_num,
        ast_num_inc_expr b max1 ->
        ast_num_inc_stmt c max2 ->
        get_ast_num_expr b = ast_num1 ->
        get_ast_num_stmt c = ast_num2 ->
        ast_num < ast_num1 -> 
        ast_num < ast_num2 -> 
        max1 < ast_num2 ->
        ast_num_inc_stmt (S_While_Loop ast_num b c) max2.


Inductive ast_num_inc_decl: object_declaration -> max_num -> Prop :=
    | Inc_Decl0: forall n0 d i max n1,
        n0 = d.(declaration_astnum) ->
        Some i = d.(initialization_expression) ->
        ast_num_inc_expr i max ->
        get_ast_num_expr i = n1 ->
        n0 < n1 ->
        ast_num_inc_decl d max
    | Inc_Decl1: forall n d,
        n = d.(declaration_astnum) ->
        None = d.(initialization_expression) ->
        ast_num_inc_decl d n.

Inductive ast_num_inc_decls: list object_declaration -> max_num -> Prop :=
    | Inc_Decls_Empty: forall n, 
        ast_num_inc_decls nil n
    | Inc_Decls1: forall d n,
        ast_num_inc_decl d n ->
        ast_num_inc_decls (d :: nil) n
    | Inc_Decls2: forall d1 n1 d2 n2 tl,
        ast_num_inc_decl d1 n1 ->
        n1 < d2.(declaration_astnum) ->
        ast_num_inc_decls (d2 :: tl) n2 ->
        ast_num_inc_decls (d1 :: (d2 :: tl)) n2.

Inductive ast_num_inc_proc_body: procedure_body -> max_num -> Prop :=
    | Inc_Proc_Body0: forall f max,
        nil = f.(procedure_declarative_part) ->
        ast_num_inc_stmt f.(procedure_statements) max ->
        f.(procedure_astnum) < get_ast_num_stmt f.(procedure_statements) ->
        ast_num_inc_proc_body f max
    | Inc_Proc_Body1: forall d tl f max1 max2,
        (d :: tl) = f.(procedure_declarative_part) ->
        ast_num_inc_decls f.(procedure_declarative_part) max1 ->
        ast_num_inc_stmt f.(procedure_statements) max2 ->
        f.(procedure_astnum) < d.(declaration_astnum) ->
        f.(procedure_astnum) < get_ast_num_stmt f.(procedure_statements) ->
        max1 < get_ast_num_stmt f.(procedure_statements) ->
        ast_num_inc_proc_body f max2.

Inductive ast_num_inc_subprogram: subprogram -> max_num -> Prop :=
    | Inc_Subprogram: forall f n ast_num,
        ast_num < f.(procedure_astnum) ->
        ast_num_inc_proc_body f n ->
        ast_num_inc_subprogram (Procedure ast_num f) n.

(*************************************************)

(** Function to test whether ast numbers labled for each ast node 
    are increasing in depth-first way;
*)

(** To import the function "leb" from the library Arith.Compare_dec; *)
Require Import Arith.Compare_dec.

Function f_ast_num_inc_expr (e: expression): option max_num :=
    match e with
    | E_Literal ast_num n => Some ast_num
    | E_Identifier ast_num x => Some ast_num
    | E_Binary_Operation ast_num op e1 e2 =>
        if (leb (get_ast_num_expr e1) ast_num) || (leb (get_ast_num_expr e2) ast_num) then
          None
        else
          match f_ast_num_inc_expr e1 with
          | Some n1 => 
              match f_ast_num_inc_expr e2 with
              | Some n2 => if leb (get_ast_num_expr e2) n1 then None else Some n2
              | None => None
              end
          | None => None
          end
    | E_Unary_Operation ast_num op e =>
        if leb (get_ast_num_expr e) ast_num then
          None
        else
          f_ast_num_inc_expr e
    end.
  
Function f_ast_num_inc_stmt (c: statement): option max_num :=
    match c with
    | S_Assignment ast_num x e =>
        if leb (get_ast_num_expr e) ast_num then None else f_ast_num_inc_expr e
    | S_Sequence ast_num c1 c2 =>
        if (leb (get_ast_num_stmt c1) ast_num) || (leb (get_ast_num_stmt c2) ast_num) then
          None
        else
          match f_ast_num_inc_stmt c1 with
          | Some n1 =>
              match f_ast_num_inc_stmt c2 with
              | Some n2 => if leb (get_ast_num_stmt c2) n1 then None else Some n2
              | None => None
              end
          | None => None
          end
    | S_If ast_num b c =>
        if (leb (get_ast_num_expr b) ast_num) || (leb (get_ast_num_stmt c) ast_num) then
          None
        else
          match f_ast_num_inc_expr b with
          | Some n1 => 
              match f_ast_num_inc_stmt c with
              | Some n2 => if leb (get_ast_num_stmt c) n1 then None else Some n2
              | None => None
              end
          | None => None
          end
    | S_While_Loop ast_num b c =>
        if (leb (get_ast_num_expr b) ast_num) || (leb (get_ast_num_stmt c) ast_num) then
          None
        else
          match f_ast_num_inc_expr b with
          | Some n1 => 
              match f_ast_num_inc_stmt c with
              | Some n2 => if leb (get_ast_num_stmt c) n1 then None else Some n2
              | None => None
              end
          | None => None
          end
    end.

Function f_ast_num_inc_decl (d: object_declaration): option max_num :=
    match d.(initialization_expression) with
    | Some i => 
        match f_ast_num_inc_expr i with
        | Some n => if leb (get_ast_num_expr i) d.(declaration_astnum) then None else Some n
        | None => None
        end
    | None => Some d.(declaration_astnum)
    end.

Function f_ast_num_inc_decls (ds: list object_declaration): option max_num :=
    match ds with
    | nil => Some 0 (* 0 is the default value for maximum ast number of empty declarations *)
    | d1 :: ds1 =>
        match f_ast_num_inc_decl d1 with
        | Some n1 =>
            match ds1 with
            | nil => Some n1
            | d2 :: ds2 => 
                if leb d2.(declaration_astnum) n1 then None else f_ast_num_inc_decls ds1
            end
        | None => None
        end
    end.

Function f_ast_num_inc_proc_body (f: procedure_body): option max_num :=
    match f.(procedure_declarative_part) with
    | nil => 
        if leb (get_ast_num_stmt f.(procedure_statements)) f.(procedure_astnum) 
        then None 
        else f_ast_num_inc_stmt f.(procedure_statements)
    | d :: ds' => 
        if leb d.(declaration_astnum) f.(procedure_astnum) || 
           leb (get_ast_num_stmt f.(procedure_statements)) f.(procedure_astnum) 
        then None
        else
          match f_ast_num_inc_decls f.(procedure_declarative_part) with
          | Some n1 =>
              if leb (get_ast_num_stmt f.(procedure_statements)) n1 
              then None
              else f_ast_num_inc_stmt f.(procedure_statements)
          | None => None
          end
    end.


Function f_ast_num_inc_subprogram (p: subprogram): option max_num :=
    match p with
    | Procedure ast_num f =>
        if leb f.(procedure_astnum) ast_num 
        then None
        else f_ast_num_inc_proc_body f
    end.

(* ===================================== *)

(** Semantical equivalence between relational and functional one 
    for checking that ast number are unique in the ast tree;
*)
Lemma expr_ast_num_exists: forall e,
    exists n, get_ast_num_expr e = n.
Proof.
    intros.
    destruct e; simpl;
    match goal with
    | [|- exists n, ?a = n] => exists a; reflexivity
    end.
Qed.

Lemma stmt_ast_num_exists: forall c,
    exists n, get_ast_num_stmt c = n.
Proof.
    intros.
    destruct c; simpl;
    match goal with
    | [|- exists n, ?a = n] => exists a; reflexivity
    end.
Qed.

Lemma leb_false_lt: forall x n y,
    leb x n || leb y n = false ->
    n < x /\ n < y.
Proof.
    intros.
    unfold "||" in H.
    remember (leb x n) as z.
    destruct z. inversion H.
    symmetry in Heqz.
    specialize (leb_complete_conv _ _ Heqz); intros hz1.
    specialize (leb_complete_conv _ _ H); intros hz2.
    split; auto.
Qed.

Lemma f_ast_num_inc_expr_correct: forall e max,
    f_ast_num_inc_expr e = Some max ->
    ast_num_inc_expr e max.
Proof.
    intros e.
    functional induction (f_ast_num_inc_expr e);
    intros max h1;
    try match goal with
    | [h: None = Some ?n |- _] => inversion h
    end.
  - inversion h1; subst.
    constructor.
  - inversion h1; subst.
    constructor.
  - inversion h1; subst.
    specialize (IHo _ e4).
    specialize (IHo0 _ e5).
    specialize (expr_ast_num_exists e1); intros hz1.
    destruct hz1.
    specialize (expr_ast_num_exists e2); intros hz2.
    destruct hz2.
    rewrite H, H0 in *.
    specialize (leb_complete_conv _ _ e6); intros hz3.
    specialize (leb_false_lt _ _ _ e3); intros hz4.
    destruct hz4 as [hz4 hz5].
    econstructor.
    exact IHo.
    exact IHo0.
    apply H. apply H0.
    assumption. assumption.
    assumption.
  - specialize (IHo _ h1).
    specialize (leb_complete_conv _ _ e2); intros hz1.
    econstructor; intuition.
Qed.

Lemma f_ast_num_inc_expr_complete: forall e max,
    ast_num_inc_expr e max ->
    f_ast_num_inc_expr e = Some max.
Proof.
    intros e max h1.
    induction h1; 
    simpl; auto.
  - rewrite H, H0 in *.
    specialize (leb_correct_conv _ _ H1); intros hz1.
    specialize (leb_correct_conv _ _ H2); intros hz2.
    specialize (leb_correct_conv _ _ H3); intros hz3.
    rewrite hz1, hz2, IHh1_1, IHh1_2.
    simpl.
    rewrite hz3.
    reflexivity.
  - rewrite H, IHh1 in *.
    specialize (leb_correct_conv _ _ H0); intros hz1.
    rewrite hz1.
    reflexivity.
Qed.

Lemma f_ast_num_inc_stmt_correct: forall c max,
    f_ast_num_inc_stmt c = Some max ->
    ast_num_inc_stmt c max.
Proof.
    intros c.
    functional induction (f_ast_num_inc_stmt c);
    intros max h1;
    try match goal with
    | [h: None = Some ?n |- _] => inversion h
    end.
  - econstructor; intuition.
    specialize (f_ast_num_inc_expr_correct _ _ h1); auto.
    specialize (leb_complete_conv _ _ e1); auto.
  - inversion h1; subst.
    specialize (IHo _ e1).
    specialize (IHo0 _ e2).
    specialize (leb_complete_conv _ _ e3); intros hz1.
    specialize (leb_false_lt _ _ _ e0); intros hz2.
    destruct hz2 as [hz2 hz3].
    econstructor; auto.
    exact IHo.
    intuition. intuition. intuition.
  - inversion h1; subst.
    specialize (IHo _ e2).
    specialize (leb_complete_conv _ _ e3); intros hz1.
    specialize (leb_false_lt _ _ _ e0); intros hz2.
    destruct hz2 as [hz2 hz3].
    econstructor; auto.
    specialize (f_ast_num_inc_expr_correct _ _ e1); intros hz4.
    exact hz4.
    intuition. intuition. intuition.
  - inversion h1; subst.
    specialize (IHo _ e2).
    specialize (leb_complete_conv _ _ e3); intros hz1.
    specialize (leb_false_lt _ _ _ e0); intros hz2.
    destruct hz2 as [hz2 hz3].
    econstructor; auto.
    specialize (f_ast_num_inc_expr_correct _ _ e1); intros hz4.
    exact hz4.
    intuition. intuition. intuition.
Qed.

Lemma f_ast_num_inc_stmt_complete: forall c max,
    ast_num_inc_stmt c max ->
    f_ast_num_inc_stmt c = Some max.
Proof.
    intros c max h1.
    induction h1;
    simpl.
  - specialize (leb_correct_conv _ _ H1); intros hz1.
    rewrite H0, hz1.
    specialize (f_ast_num_inc_expr_complete _ _ H); auto.
  - rewrite H, H0 in *.
    specialize (leb_correct_conv _ _ H1); intros hz1.
    specialize (leb_correct_conv _ _ H2); intros hz2.
    specialize (leb_correct_conv _ _ H3); intros hz3.
    rewrite hz1, hz2, IHh1_1, IHh1_2, hz3.
    simpl. reflexivity.
  - rewrite H0, H1 in *.
    specialize (leb_correct_conv _ _ H2); intros hz1.
    specialize (leb_correct_conv _ _ H3); intros hz2.
    specialize (leb_correct_conv _ _ H4); intros hz3.    
    specialize (f_ast_num_inc_expr_complete _ _ H); intros hz4.
    rewrite hz1, hz2, hz4, IHh1, hz3.
    simpl; auto.
  - rewrite H0, H1 in *.
    specialize (leb_correct_conv _ _ H2); intros hz1.
    specialize (leb_correct_conv _ _ H3); intros hz2.
    specialize (leb_correct_conv _ _ H4); intros hz3.    
    specialize (f_ast_num_inc_expr_complete _ _ H); intros hz4.
    rewrite hz1, hz2, hz4, IHh1, hz3.
    simpl; auto.
Qed.

Lemma f_ast_num_inc_decl_correct: forall d max,
    f_ast_num_inc_decl d = Some max ->
    ast_num_inc_decl d max.
Proof.
    intros d.
    functional induction (f_ast_num_inc_decl d);
    intros max h1;
    try match goal with
    | [h: None = Some ?n |- _] => inversion h
    end.
  - inversion h1; subst.
    specialize (f_ast_num_inc_expr_correct _ _ e0); intros hz1.
    specialize (leb_complete_conv _ _ e1); intros hz2.
    econstructor; auto.
    symmetry in e; exact e.
    assumption. intuition.
  - inversion h1; subst.
    constructor; intuition.
Qed.

Lemma f_ast_num_inc_decl_complete: forall d max,
    ast_num_inc_decl d max ->
    f_ast_num_inc_decl d = Some max.
Proof.
    intros d max h1.
    induction h1;
    unfold f_ast_num_inc_decl.
  - symmetry in H, H0.
    rewrite H0, H, H2.
    specialize (f_ast_num_inc_expr_complete _ _ H1); intros hz1.
    specialize (leb_correct_conv _ _ H3); intros hz2.
    rewrite hz1, hz2.
    reflexivity.
  - rewrite <- H0.
    intuition.
Qed.

(** for declaration part with at least one declaration definition; *)
Lemma f_ast_num_inc_decls_correct: forall tl d max,
    f_ast_num_inc_decls (d :: tl) = Some max ->
    ast_num_inc_decls (d :: tl) max.
Proof.
    induction tl;
    intros d max h1.
  - constructor.
    simpl in h1.
    remember (f_ast_num_inc_decl d) as x.
    destruct x.
    + inversion h1; subst.
      symmetry in Heqx. 
      specialize (f_ast_num_inc_decl_correct _ _ Heqx); auto.
    + inversion h1.
  - simpl in h1.
    remember (f_ast_num_inc_decl d) as x.
    symmetry in Heqx.
    destruct x.
    + remember (leb (declaration_astnum a) m) as y.
      symmetry in Heqy.
      destruct y. inversion h1.
      specialize (f_ast_num_inc_decl_correct _ _ Heqx); intros hz1.
      specialize (leb_complete_conv _ _ Heqy); intros hz2.
      econstructor.
      exact hz1. exact hz2.
      specialize (IHtl _ _ h1).
      assumption.
    + inversion h1.
Qed.

Lemma f_ast_num_inc_decls_complete: forall tl d max,
    ast_num_inc_decls (d :: tl) max ->
    f_ast_num_inc_decls (d :: tl) = Some max.
Proof.
    induction tl;
    intros d max h1;
    inversion h1; subst;
    simpl.
  - specialize (f_ast_num_inc_decl_complete _ _ H0); intros hz1.
    rewrite hz1.
    reflexivity.
  - specialize (IHtl _ _ H5).
    specialize (f_ast_num_inc_decl_complete _ _ H2); intros hz1.
    specialize (leb_correct_conv _ _ H4); intros hz2.
    rewrite hz1, hz2.
    assumption.
Qed.

Lemma f_ast_num_inc_proc_body_correct: forall f max,
    f_ast_num_inc_proc_body f = Some max ->
    ast_num_inc_proc_body f max.
Proof.
    intros f.
    functional induction (f_ast_num_inc_proc_body f);
    intros max h1;
    try match goal with
    | [h: None = Some ?n |- _] => inversion h
    end.
  - econstructor; auto.
    specialize (f_ast_num_inc_stmt_correct _ _ h1); auto.
    specialize (leb_complete_conv _ _ e0); auto.
  - rewrite e in *.
    specialize (f_ast_num_inc_decls_correct _ _ _ e1); intros hz1.
    specialize (f_ast_num_inc_stmt_correct _ _ h1); intros hz2.
    specialize (leb_false_lt _ _ _ e0); intros hz3.
    destruct hz3 as [hz3 hz4].
    specialize (leb_complete_conv _ _ e2); intros hz5.
    eapply Inc_Proc_Body1.
    symmetry in e; exact e.
    rewrite e; exact hz1.
    assumption. assumption.
    assumption. assumption.
Qed.

Lemma f_ast_num_inc_proc_body_complete: forall f max,
    ast_num_inc_proc_body f max ->
    f_ast_num_inc_proc_body f = Some max.
Proof.
    intros f max h1.
    induction h1;
    unfold f_ast_num_inc_proc_body;
    rewrite <- H.
  - specialize (leb_correct_conv _ _ H1); intros hz1.
    rewrite hz1.
    specialize (f_ast_num_inc_stmt_complete _ _ H0); auto.
  - specialize (leb_correct_conv _ _ H2); intros hz1.
    specialize (leb_correct_conv _ _ H3); intros hz2.
    specialize (leb_correct_conv _ _ H4); intros hz3.
    rewrite <- H in H0.
    specialize (f_ast_num_inc_decls_complete _ _ _ H0); intros hz4.
    specialize (f_ast_num_inc_stmt_complete _ _ H1); intros hz5.
    rewrite hz1, hz2, hz4, hz5, hz3; simpl.
    reflexivity.
Qed.

Lemma f_ast_num_inc_subprogram_correct: forall p max,
    f_ast_num_inc_subprogram p = Some max ->
    ast_num_inc_subprogram p max.
Proof.
    intros p;
    functional induction (f_ast_num_inc_subprogram p);
    intros max h1.
    inversion h1.
    constructor.
    specialize (leb_complete_conv _ _ e0); auto.
    specialize (f_ast_num_inc_proc_body_correct _ _ h1); auto.
Qed.

Lemma f_ast_num_inc_subprogram_complete: forall p max,
    ast_num_inc_subprogram p max ->
    f_ast_num_inc_subprogram p = Some max.
Proof.
    intros p max h1.
    induction h1.
    simpl.
    specialize (leb_correct_conv _ _ H); intros hz1.
    specialize (f_ast_num_inc_proc_body_complete _ _ H0); intros hz2.
    rewrite hz1, hz2.
    reflexivity.
Qed.

(* ===================================== *)

(** ** Generate the run-time-check flags *)

(** the run-time checks are stored in a list indexed with ast number *)
Definition check_points :=  list (astnum * run_time_check_set).

Function fetch_cks (id : astnum) (m : check_points): run_time_check_set := 
    match m with 
    | (id', cks') :: m' =>
      if beq_nat id id' then
        cks'
      else 
        fetch_cks id m' 
    | nil => nil
    end.

(** this's used to constrain that all ast numbers used in check_points
    are smaller than a certain number;
*)
Inductive ast_nums_lt: check_points -> astnum -> Prop := 
    | lt1: forall ls n ast_num ck,
        ast_nums_lt ls n ->
        ast_num < n ->
        ast_nums_lt ((ast_num, ck) ::ls) n
    | lt2: forall n,
        ast_nums_lt nil n.

(** the functional version for ast_nums_lt *)
Function f_ast_nums_lt (ckp: check_points) (n: astnum): bool :=
    match ckp with
    | (ast_num, ck) :: tl => 
        if leb n ast_num then false else f_ast_nums_lt tl n
    | nil => true
    end.

(** soem useful lemmas about ast_nums_lt *)
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
(** compute run time check flags for each expression ast node according 
    to the checking rules, and the results are stored in a data structure 
    of type check_points;
*)
Inductive check_generator_expr: check_points -> expression -> check_points -> Prop :=
    | CG_Literal: forall ast_num n ls,
        check_generator_expr ls (E_Literal ast_num n) ls
    | CG_Identifier: forall ast_num x ls,
        check_generator_expr ls (E_Identifier ast_num x) ls
    | CG_Binary_Operation_None: forall ls e1 ls1 e2 ls2 ast_num op,
        check_flags (E_Binary_Operation ast_num op e1 e2) nil -> 
        check_generator_expr ls e1 ls1 ->
        check_generator_expr ls1 e2 ls2 ->
        check_generator_expr ls (E_Binary_Operation ast_num op e1 e2) ls2
    | CG_Binary_Operation: forall ls e1 ls1 e2 ls2 ast_num op cks,
        check_flags (E_Binary_Operation ast_num op e1 e2) cks ->
        cks <> nil ->
        check_generator_expr ((ast_num, cks) :: ls) e1 ls1 ->
        check_generator_expr ls1 e2 ls2 ->
        check_generator_expr ls (E_Binary_Operation ast_num op e1 e2) ls2
    | CG_Unary_Operation: forall ls e ls1 ast_num op,
        check_generator_expr ls e ls1 ->
        check_generator_expr ls (E_Unary_Operation ast_num op e) ls1.

(** *** generate run-time-check flags for statements *)
(** For the SPARK 2014 subset that we are working on, we only consider 
    the division by zero check and overflow check. Right now we have
    only implemented the division by zero check, and we will extend it 
    with overflow check later;
    So here, the check for each statement is none, but it is extensible 
    to includes all necessary checks in the statements in the future; 
 *)
Inductive check_generator_stmt: check_points -> statement -> check_points -> Prop :=
    | CG_Assignment: forall ls1 e ls2 ast_num x,
        check_generator_expr ls1 e ls2 ->
        check_generator_stmt ls1 (S_Assignment ast_num x e) ls2
    | CG_Sequence: forall ls1 c1 ls2 c2 ls3 ast_num,
        check_generator_stmt ls1 c1 ls2 ->
        check_generator_stmt ls2 c2 ls3 ->
        check_generator_stmt ls1 (S_Sequence ast_num c1 c2) ls3
    | CG_If: forall ls1 b ls2 c ls3 ast_num,
        check_generator_expr ls1 b ls2 ->
        check_generator_stmt ls2 c ls3 ->
        check_generator_stmt ls1 (S_If ast_num b c) ls3
    | CG_While_Loop: forall ls1 b ls2 c ls3 ast_num,
        check_generator_expr ls1 b ls2 ->
        check_generator_stmt ls2 c ls3 ->        
        check_generator_stmt ls1 (S_While_Loop ast_num b c) ls3.


Inductive check_generator_decl: check_points -> object_declaration -> check_points -> Prop :=
    | CG_Decl0: forall d ls,
        None = d.(initialization_expression) ->
        check_generator_decl ls d ls
    | CG_Decl1: forall i d ls1 ls2,
        Some i = d.(initialization_expression) ->
        check_generator_expr ls1 i ls2 ->
        check_generator_decl ls1 d ls2.

Inductive check_generator_decls: check_points -> list object_declaration -> check_points -> Prop :=
    | CG_Decls_Empty: forall ls,
        check_generator_decls ls nil ls
    | CG_Decls: forall ls d ls'0 tl ls',
        check_generator_decl ls d ls'0 ->
        check_generator_decls ls'0 tl ls' ->
        check_generator_decls ls (d :: tl) ls'.

Inductive check_generator_proc_body: check_points -> procedure_body -> check_points -> Prop :=
    | CG_Proc_Body: forall ls1 f ls2 ls3,
        check_generator_decls ls1 f.(procedure_declarative_part) ls2 ->
        check_generator_stmt ls2 f.(procedure_statements) ls3 ->
        check_generator_proc_body ls1 f ls3.

Inductive check_generator_subprogram: check_points -> subprogram -> check_points -> Prop :=
    | CG_Subprogram: forall ls1 f ls2 ast_num,
        check_generator_proc_body ls1 f ls2 ->
        check_generator_subprogram ls1 (Procedure ast_num f) ls2.


(* =============================== *)

(** Function for run-time checks generation according to checking rules *)

Function f_check_generator_expr (ckp: check_points) (e: expression): check_points :=
    match e with
    | E_Literal ast_num n => ckp
    | E_Identifier ast_num x => ckp
    | E_Binary_Operation ast_num op e1 e2 => 
        match f_check_flags e with
        | nil =>
            let ckp' := f_check_generator_expr ckp e1 in
            f_check_generator_expr ckp' e2      
        | cks => 
            let ckp' := f_check_generator_expr ((ast_num, cks) :: ckp) e1 in
            f_check_generator_expr ckp' e2
        end
    | E_Unary_Operation ast_num op e0 =>
        f_check_generator_expr ckp e0
    end.

Function f_check_generator_stmt (ckp: check_points) (c: statement): check_points :=
    match c with
    | S_Assignment ast_num x e => f_check_generator_expr ckp e
    | S_Sequence ast_num c1 c2 =>
        let ckp' := f_check_generator_stmt ckp c1 in
        f_check_generator_stmt ckp' c2
    | S_If ast_num b c0 => 
        let ckp' := f_check_generator_expr ckp b in
        f_check_generator_stmt ckp' c0
    | S_While_Loop ast_num b c0 => 
        let ckp' := f_check_generator_expr ckp b in
        f_check_generator_stmt ckp' c0
    end.

Function f_check_generator_decl (ckp: check_points) (d: object_declaration): check_points :=
    match d.(initialization_expression) with
    | None => ckp
    | Some i => f_check_generator_expr ckp i
    end.

Function f_check_generator_decls (ckp: check_points) (ds: list object_declaration): check_points :=
    match ds with
    | nil => ckp
    | d :: tl => 
        let ckp' := f_check_generator_decl ckp d in
        f_check_generator_decls ckp' tl
    end.

Function f_check_generator_proc_body (ckp: check_points) (f: procedure_body): check_points :=
    let ckp' := f_check_generator_decls ckp f.(procedure_declarative_part) in
    f_check_generator_stmt ckp' f.(procedure_statements).

Function f_check_generator_subprogram (ckp: check_points) (p: subprogram): check_points :=
    match p with
    | Procedure ast_num f => f_check_generator_proc_body ckp f
    end.

(** f_checks_match can be used to check whether GNAT frontend generated 
    run time checks are consistent with the checks required by checking 
    rules; 
*)

Function f_check_match (ck: run_time_checks) (ck': run_time_checks): bool :=
    match ck, ck' with
    | Do_Division_Check, Do_Division_Check => true
    | Do_Overflow_Check, Do_Overflow_Check => true
    | _, _ => false
    end.

Function f_check_list_match (cks: run_time_check_set) (cks': run_time_check_set): bool :=
    match cks, cks' with
    | nil, nil => true
    | (x :: xs), (y :: ys) =>
        match f_check_match x y with
        | true => f_check_list_match xs ys
        | false => false
        end
    | _, _ => false
    end.

Function f_checks_match (required_checks: check_points) (actual_checks: check_points): bool :=
    match required_checks, actual_checks with
    | nil, nil => true
    | (ck :: cks), (ck' :: cks') => 
        match ck, ck' with
        | (astnum, check), (astnum', check') =>
            if beq_nat astnum astnum' && f_check_list_match check check' 
            then f_checks_match cks cks' 
            else false
        end
    | _, _ => false
    end.

(* =============================== *)

(** Semantical equivalence between functional and relational style 
    for run time check flags generation; 
*)

Lemma f_ast_nums_lt_correct: forall ckp n,
    f_ast_nums_lt ckp n = true ->
    ast_nums_lt ckp n.
Proof.
    induction ckp;
    intros n h1.
  - constructor.
  - simpl in h1.
    remember a as x.
    destruct x.
    remember (leb n a0) as y.
    destruct y. inversion h1.
    specialize (IHckp _ h1).
    symmetry in Heqy. specialize (leb_complete_conv _ _ Heqy); intros hz1.
    econstructor; auto.
Qed.

Lemma f_ast_nums_lt_complete: forall ckp n,
    ast_nums_lt ckp n ->
    f_ast_nums_lt ckp n = true.
Proof.
    induction ckp;
    intros n h1.
  - auto.
  - remember a as x.
    destruct x.
    inversion h1; subst.
    specialize (IHckp _ H3).
    simpl.
    specialize (leb_correct_conv _ _ H4); intros hz1.
    rewrite hz1.
    assumption.
Qed.


Lemma f_check_generator_expr_correct: forall ckp e ckp',
    f_check_generator_expr ckp e = ckp' ->
    check_generator_expr ckp e ckp'.
Proof.
    intros ckp e.
    functional induction (f_check_generator_expr ckp e);
    intros ckp' h1.
  - rewrite <- h1.
    constructor.
  - rewrite <- h1.
    constructor.
  - specialize (IHc0 _ h1).
    eapply CG_Binary_Operation_None.
    specialize (f_check_flags_correct _ _ e3); auto.
    specialize (IHc (f_check_generator_expr ckp e1)).
    intuition.
    exact H. assumption.
  - specialize (IHc0 _ h1).
    remember (f_check_flags (E_Binary_Operation ast_num op e1 e2)) as x.
    symmetry in Heqx.
    destruct x; inversion y.
    eapply CG_Binary_Operation.
    specialize (f_check_flags_correct _ _ Heqx); intros hz1.
    exact hz1.
    rm_always_true.
    specialize (IHc (f_check_generator_expr ((ast_num, r :: x) :: ckp) e1)).
    intuition.
    exact H. assumption.
  - specialize (IHc _ h1).
    constructor.
    assumption.
Qed.

Lemma f_check_generator_expr_complete: forall ckp e ckp',
    check_generator_expr ckp e ckp' ->
    f_check_generator_expr ckp e = ckp'.
Proof.
    intros ckp e ckp' h1.
    induction h1;
    simpl; auto;
    destruct op; 
    inversion H; subst; auto;
    try rm_false_hyp.
Qed.

Lemma f_check_generator_stmt_correct: forall ckp c ckp',
    f_check_generator_stmt ckp c = ckp' ->
    check_generator_stmt ckp c ckp'.
Proof.
    intros ckp c.
    functional induction (f_check_generator_stmt ckp c);
    intros ckp' h1.
  - constructor.
    specialize (f_check_generator_expr_correct _ _ _ h1); auto.
  - specialize (IHc1 _ h1).
    specialize (IHc0 (f_check_generator_stmt ckp c1)).
    intuition.
    econstructor.
    exact H. assumption.
  - specialize (IHc0 _ h1).
    econstructor.
    assert (hz1: f_check_generator_expr ckp b = f_check_generator_expr ckp b); auto.
    specialize (f_check_generator_expr_correct _ _ _ hz1); intros hz2.
    exact hz2.
    assumption.
  - specialize (IHc0 _ h1).
    econstructor.
    assert (hz1: f_check_generator_expr ckp b = f_check_generator_expr ckp b); auto.
    specialize (f_check_generator_expr_correct _ _ _ hz1); intros hz2.
    exact hz2.
    assumption.
Qed.

Lemma f_check_generator_stmt_complete: forall ckp c ckp',
    check_generator_stmt ckp c ckp' ->
    f_check_generator_stmt ckp c = ckp'.
Proof.
    intros ckp c ckp' h1.
    induction h1; simpl.
  - specialize (f_check_generator_expr_complete _ _ _ H); 
    auto.
  - rewrite IHh1_1, IHh1_2.
    reflexivity.
  - specialize (f_check_generator_expr_complete _ _ _ H); intros hz1.
    rewrite hz1.
    assumption.
  - specialize (f_check_generator_expr_complete _ _ _ H); intros hz1.
    rewrite hz1.
    assumption.
Qed.

Lemma f_check_generator_decl_correct: forall ckp d ckp',
    f_check_generator_decl ckp d = ckp' ->
    check_generator_decl ckp d ckp'.
Proof.
    intros ckp d;
    functional induction (f_check_generator_decl ckp d);
    intros ckp' h1.
  - rewrite <- h1.
    constructor.
    auto.
  - econstructor.
    symmetry in e; exact e.
    specialize (f_check_generator_expr_correct _ _ _ h1); auto.
Qed.

Lemma f_check_generator_decl_complete: forall ckp d ckp',
    check_generator_decl ckp d ckp' ->
    f_check_generator_decl ckp d = ckp'.
Proof.
    intros ckp d ckp' h1.
    induction h1;
    unfold f_check_generator_decl;
    rewrite <- H; auto.
    specialize (f_check_generator_expr_complete _ _ _ H0); auto.
Qed.

Lemma f_check_generator_decls_correct: forall tl ckp d ckp',
    f_check_generator_decls ckp (d :: tl) = ckp' ->
    check_generator_decls ckp (d :: tl) ckp'.
Proof.
    induction tl;
    intros ckp d ckp' h1.
  - simpl in h1.
    specialize (f_check_generator_decl_correct _ _ _ h1); intros hz1.
    econstructor.
    exact hz1. constructor.
  - simpl in h1.
    specialize (IHtl _ _ _ h1).
    econstructor.
    assert (hz1: f_check_generator_decl ckp d = f_check_generator_decl ckp d); auto.
    specialize (f_check_generator_decl_correct _ _ _ hz1); intros hz2.
    exact hz2.
    assumption.
Qed.

Lemma f_check_generator_decls_complete: forall tl ckp d ckp',
    check_generator_decls ckp (d :: tl) ckp' ->
    f_check_generator_decls ckp (d :: tl) = ckp'.
Proof.
    induction tl; 
    intros ckp d ckp' h1;
    simpl.
  - inversion h1; subst.
    inversion H4; subst.
    specialize (f_check_generator_decl_complete _ _ _ H2); auto.
  - inversion h1; subst.
    specialize (IHtl _ _ _ H4).
    specialize (f_check_generator_decl_complete _ _ _ H2); intros hz1.
    rewrite hz1. assumption.
Qed.

Lemma f_check_generator_proc_body_correct: forall ckp f ckp',
    f_check_generator_proc_body ckp f = ckp' ->
    check_generator_proc_body ckp f ckp'.
Proof.
    intros ckp f;
    functional induction (f_check_generator_proc_body ckp f);
    intros ckp' h1.
    remember (procedure_declarative_part f) as x.
    destruct x.
    econstructor.
    rewrite <- Heqx. constructor.
    simpl in h1.
    specialize (f_check_generator_stmt_correct _ _ _ h1); auto.
    econstructor.
    rewrite <- Heqx.
    assert (hz1: (f_check_generator_decls ckp (o :: x)) = (f_check_generator_decls ckp (o :: x))); auto.
    specialize (f_check_generator_decls_correct _ _ _ _ hz1); intros hz2.
    exact hz2.
    specialize (f_check_generator_stmt_correct _ _ _ h1); auto.
Qed.

Lemma f_check_generator_proc_body_complete: forall ckp f ckp',
    check_generator_proc_body ckp f ckp' ->
    f_check_generator_proc_body ckp f = ckp'.
Proof.
    intros ckp f ckp' h1.
    induction h1.
    remember (procedure_declarative_part f) as x.
    destruct x.
  - inversion H; subst.
    unfold f_check_generator_proc_body.
    rewrite <- Heqx. simpl.
    specialize (f_check_generator_stmt_complete _ _ _ H0); auto.
  - unfold f_check_generator_proc_body.
    rewrite <- Heqx. 
    specialize (f_check_generator_decls_complete _ _ _ _ H); intros hz1.
    rewrite hz1.
    specialize (f_check_generator_stmt_complete _ _ _ H0); auto.
Qed.

Lemma f_check_generator_subprogram_correct: forall ckp p ckp',
    f_check_generator_subprogram ckp p = ckp' ->
    check_generator_subprogram ckp p ckp'.
Proof.
    intros ckp p;
    functional induction (f_check_generator_subprogram ckp p);
    intros ckp' h1.
    constructor.
    specialize (f_check_generator_proc_body_correct _ _ _ h1); auto.
Qed.

Lemma f_check_generator_subprogram_complete: forall ckp p ckp',
    check_generator_subprogram ckp p ckp' ->
    f_check_generator_subprogram ckp p = ckp'.
Proof.
    intros ckp p ckp' h1.
    induction h1.
    simpl.
    specialize (f_check_generator_proc_body_complete _ _ _ H); auto.
Qed.


(** ** Semantics with run-time-checks *)

(** the semantics for expressions evaluation, where cps is passed in 
    as a parameter telling whether a checks are needed to be performed 
    before executing the expression ast node;
*)
Inductive eval_expr_with_checks (cps: check_points): stack -> expression -> return_val -> Prop :=
    | eval_Literal: forall l v s ast_num,
        eval_literal l = v ->
        eval_expr_with_checks cps s (E_Literal ast_num l) (Val_Normal v)
    | eval_Identifier: forall x s v ast_num,
        fetch x s = Some v ->
        eval_expr_with_checks cps s (E_Identifier ast_num x) (Val_Normal v)
    | eval_Binary_Operation1: forall s e1 ast_num op e2,
        eval_expr_with_checks cps s e1 Val_Run_Time_Error ->
        eval_expr_with_checks cps s (E_Binary_Operation ast_num op e1 e2) Val_Run_Time_Error
    | eval_Binary_Operation2: forall s e1 v1 e2 ast_num op,
        eval_expr_with_checks cps s e1 (Val_Normal v1) ->
        eval_expr_with_checks cps s e2 Val_Run_Time_Error ->
        eval_expr_with_checks cps s (E_Binary_Operation ast_num op e1 e2) Val_Run_Time_Error
    | eval_Binary_Operation3: forall s e1 v1 e2 v2 cks ast_num op,
        eval_expr_with_checks cps s e1 (Val_Normal v1) ->
        eval_expr_with_checks cps s e2 (Val_Normal v2) ->
        fetch_cks ast_num cps = cks ->
        do_flagged_checks cks op v1 v2 false ->
        eval_expr_with_checks cps s (E_Binary_Operation ast_num op e1 e2) Val_Run_Time_Error
    | eval_Binary_Operation4: forall s e1 v1 e2 v2 cks ast_num op v,
        eval_expr_with_checks cps s e1 (Val_Normal v1) ->
        eval_expr_with_checks cps s e2 (Val_Normal v2) ->
        fetch_cks ast_num cps = cks -> 
        do_flagged_checks cks op v1 v2 true ->
        eval_bin_expr op v1 v2 v ->
        eval_expr_with_checks cps s (E_Binary_Operation ast_num op e1 e2) (Val_Normal v)
    | eval_Unary_Operation1: forall s e ast_num op,
        eval_expr_with_checks cps s e Val_Run_Time_Error ->
        eval_expr_with_checks cps s (E_Unary_Operation ast_num op e) Val_Run_Time_Error
    | eval_Unary_Operation2: forall s e v ast_num op v1,
        eval_expr_with_checks cps s e (Val_Normal v) ->
        eval_unary_expr op v v1 ->
        eval_expr_with_checks cps s (E_Unary_Operation ast_num op e) (Val_Normal v1).


(** 
    it's similar to the eval_expr_with_checks: cps is used to denote 
    whether a check is needed to be performed before executing the 
    statement; right now, we only consider the division and overflow checks
    for expressions, and there are no checks enfornced on the statements;
    Note: only division by zero check has been implemented, overflow check
          will be added later;
*)
Inductive eval_stmt_with_checks (cps: check_points): stack -> statement -> state -> Prop :=
    | eval_Assignment1: forall s e ast_num x,
        eval_expr_with_checks cps s e Val_Run_Time_Error ->
        eval_stmt_with_checks cps s (S_Assignment ast_num x e) S_Run_Time_Error
    | eval_Assignment2: forall s e v x s1 ast_num,
        eval_expr_with_checks cps s e (Val_Normal v) ->
        update s x (Value v) = Some s1 -> 
        eval_stmt_with_checks cps s (S_Assignment ast_num x e) (S_Normal s1)
    | eval_Sequence1: forall s c1 ast_num c2,
        eval_stmt_with_checks cps s c1 S_Run_Time_Error ->
        eval_stmt_with_checks cps s (S_Sequence ast_num c1 c2) S_Run_Time_Error
    | eval_Sequence2: forall ast_num s s1 s2 c1 c2,
        eval_stmt_with_checks cps s c1 (S_Normal s1) ->
        eval_stmt_with_checks cps s1 c2 s2 ->
        eval_stmt_with_checks cps s (S_Sequence ast_num c1 c2) s2
    | eval_If: forall s b ast_num c,
        eval_expr_with_checks cps s b Val_Run_Time_Error ->
        eval_stmt_with_checks cps s (S_If ast_num b c) S_Run_Time_Error
    | eval_If_True: forall s b c s1 ast_num,
        eval_expr_with_checks cps s b (Val_Normal (Bool true)) ->
        eval_stmt_with_checks cps s c s1 ->
        eval_stmt_with_checks cps s (S_If ast_num b c) s1
    | eval_If_False: forall s b ast_num c,
        eval_expr_with_checks cps s b (Val_Normal (Bool false)) ->
        eval_stmt_with_checks cps s (S_If ast_num b c) (S_Normal s)
    | eval_While_Loop: forall s b ast_num c,
        eval_expr_with_checks cps s b Val_Run_Time_Error ->
        eval_stmt_with_checks cps s (S_While_Loop ast_num b c) S_Run_Time_Error
    | eval_While_Loop_True1: forall s b c ast_num,
        eval_expr_with_checks cps s b (Val_Normal (Bool true)) ->
        eval_stmt_with_checks cps s c S_Run_Time_Error ->
        eval_stmt_with_checks cps s (S_While_Loop ast_num b c) S_Run_Time_Error
    | eval_While_Loop_True2: forall s b c s1 ast_num s2,
        eval_expr_with_checks cps s b (Val_Normal (Bool true)) ->
        eval_stmt_with_checks cps s c (S_Normal s1) ->
        eval_stmt_with_checks cps s1 (S_While_Loop ast_num b c) s2 ->
        eval_stmt_with_checks cps s (S_While_Loop ast_num b c) s2
    | eval_While_Loop_False: forall s b ast_num c,
        eval_expr_with_checks cps s b (Val_Normal (Bool false)) ->
        eval_stmt_with_checks cps s (S_While_Loop ast_num b c) (S_Normal s).

(** variables declaration with initialization expression are a little 
    defferent from the assignments:
    for variable declaration, we add the new declared variable with 
    its initialization value to the initial stack, because all declared 
    variables have unique names; for assignment, we update the initial 
    stack by assigning new value to its existing variable;
*)
Inductive eval_decl_with_checks (cps: check_points): stack -> object_declaration -> state -> Prop :=
    | eval_Decl0: forall x d s,
        x = d.(object_name) ->
        None = d.(initialization_expression) ->
        eval_decl_with_checks cps s d (S_Normal ((x, Undefined) :: s))
    | eval_Decl1: forall i d s,
        Some i = d.(initialization_expression) ->
        eval_expr_with_checks cps s i Val_Run_Time_Error ->
        eval_decl_with_checks cps s d S_Run_Time_Error
    | eval_Decl2: forall x d i s v,
        x = d.(object_name) ->
        Some i = d.(initialization_expression) ->
        eval_expr_with_checks cps s i (Val_Normal v) ->
        eval_decl_with_checks cps s d (S_Normal ((x, Value v) :: s)).

Inductive eval_decls_with_checks (cps: check_points): 
    stack -> list object_declaration -> state -> Prop :=
    | eval_Decls_Empty: forall s,
        eval_decls_with_checks cps s nil (S_Normal s)
    | eval_Decls0: forall s d tl,
        eval_decl_with_checks cps s d S_Run_Time_Error ->
        eval_decls_with_checks cps s (d :: tl) S_Run_Time_Error
    | eval_Decls1: forall s d s'0 tl s',
        eval_decl_with_checks cps s d (S_Normal s'0) ->
        eval_decls_with_checks cps s'0 tl s' ->
        eval_decls_with_checks cps s (d :: tl) s'.

Inductive eval_proc_body_with_checks (cps: check_points): 
    stack -> procedure_body -> state -> Prop :=
    | eval_Proc_Body0: forall s f,
        eval_decls_with_checks cps s f.(procedure_declarative_part) S_Run_Time_Error ->
        eval_proc_body_with_checks cps s f S_Run_Time_Error
    | eval_Proc_Body1: forall s f s'0 s',
        eval_decls_with_checks cps s f.(procedure_declarative_part) (S_Normal s'0) ->
        eval_stmt_with_checks cps s'0 f.(procedure_statements) s' ->
        eval_proc_body_with_checks cps s f s'.

Inductive eval_subprogram_with_checks (cps: check_points): stack -> subprogram -> state -> Prop :=
    | eval_Subprogram: forall s1 f s2 ast_num,
        eval_proc_body_with_checks cps s1 f s2 ->
        eval_subprogram_with_checks cps s1 (Procedure ast_num f) s2.


(** some basic lemmas *)
(** eval_stmt_with_checks returns either a normal value or a 
    run time error when the run time check fails; 
*)
Lemma eval_expr_with_checks_state: forall ls s e v,
    eval_expr_with_checks ls s e v ->
    (exists v', v = Val_Normal v') \/ v = Val_Run_Time_Error.
Proof.
    intros.
    induction H;
    try match goal with
    | [ |- (exists v' : value, Val_Normal ?v = Val_Normal v') \/ _ ] => left; exists v; reflexivity
    | [ |- _ \/ ?A = ?A ] => right; reflexivity
    end.
Qed.

(** 
   all ast numbers are unique: in a AST tree, parent node's ast number 
   is smaller than children node's ast number.
   (get_ast_num_expr e) returns the ast number for expression e, and 
   max is the maximum ast number used in e, if e has no subexpression, 
   then max is the same as (get_ast_num_expr e), otherwise, max is maximum
   ast number of its subexpressions, so (get_ast_num_expr e) should be 
   less and equal than max;
*)
Lemma ast_num_bound_expr: forall e max,
    ast_num_inc_expr e max ->
    get_ast_num_expr e <= max.
Proof.
    intros e max h.
    induction h; simpl; intuition.
Qed.

(** 
    checks are computed according to the checking rules for expression 
    e and its subexpressions, the results are stored in cks indexed by 
    expression's and its subexpression's ast numbers, because max is the 
    maximum ast number, so all ast numbers in cks should be less than 
    (max + 1);
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
    specialize (IHh1_1 _ _ H11 hz1).
    assert(hz: max1 + 1 <= get_ast_num_expr e2); intuition.
    specialize (ast_nums_lt_trans0 _ _ _ IHh1_1 hz); intros hz3.
    specialize (IHh1_2 _ _ H12 hz3).
    assumption.
  - specialize (ast_nums_lt_trans _ _ _ h3 H1); intros hz1.
    specialize (ast_nums_lt_add _ _ _ cks1 H1 hz1); intros hz2.
    specialize (IHh1_1 _ _ H12 hz2).
    assert(hz: max1 + 1 <= get_ast_num_expr e2); intuition.
    specialize (ast_nums_lt_trans0 _ _ _ IHh1_1 hz); intros hz3.
    specialize (IHh1_2 _ _ H13 hz3).
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


Lemma ast_num_bound_decl: forall d max,
    ast_num_inc_decl d max ->
    d.(declaration_astnum) <= max.
Proof.
    intros d max h.
    induction h; simpl; intuition.
    specialize (ast_num_bound_expr _ _ H1); intros hz1.
    intuition.
Qed.

(** local variable declarations with at least one declaration; *)
Lemma ast_num_bound_decls: forall d tl max,
    ast_num_inc_decls (d :: tl) max ->
    d.(declaration_astnum) <= max.
Proof.
    intros.
    remember (d :: tl) as ds.
    revert Heqds. revert d tl.
    induction H; intros;
    inversion Heqds; subst.
    apply (ast_num_bound_decl _ _ H); auto.
    specialize (IHast_num_inc_decls d2 tl); intuition.
    specialize (ast_num_bound_decl _ _ H); intros hz1. 
    intuition.
Qed.

Lemma ast_num_max_decl: forall d max cks0 cks1,
    ast_num_inc_decl d max ->
    check_generator_decl cks0 d cks1 ->
    ast_nums_lt cks0 d.(declaration_astnum) ->
    ast_nums_lt cks1 (max + 1).
Proof.
    intros d max cks0 cks1 h1.
    revert cks0 cks1.
    induction h1;
    intros cks0 cks1 h2 h3;
    simpl in h3; inversion h2; subst.
  - specialize (ast_num_bound_expr _ _ H1); intros hz1.
    specialize (ast_nums_lt_trans _ _ _ h3 H3); intros hz2.
    assert (hz3: get_ast_num_expr i < max + 1); intuition.
    specialize (ast_nums_lt_trans _ _ _ hz2 hz3); intros hz4.
    assumption.
  - rewrite <- H0 in H4; inversion H4; subst.
    specialize (ast_nums_lt_trans _ _ _ h3 H3); intros hz1.
    specialize (ast_num_max_expr _ _ _ _ H1 H5 hz1); auto.
  - assert (hz1: declaration_astnum d < declaration_astnum d + 1); intuition.
    specialize (ast_nums_lt_trans _ _ _ h3 hz1); auto.
  - rewrite <- H0 in H1; inversion H1.
Qed.

Lemma ast_num_max_decls: forall d tl max cks0 cks1,
    ast_num_inc_decls (d :: tl) max ->
    check_generator_decls cks0 (d :: tl) cks1 ->
    ast_nums_lt cks0 d.(declaration_astnum) ->
    ast_nums_lt cks1 (max + 1).
Proof.
    intros d tl max cks0 cks1 h1.
    revert cks0 cks1.
    remember (d :: tl) as ds. revert Heqds. revert d tl.
    induction h1;
    intros d'0 tl'0 h2 cks0 cks1 h3 h4;
    inversion h2; subst.
  - inversion h3; subst.
    inversion H5; subst.
    specialize (ast_num_max_decl _ _ _ _ H H3 h4); auto.
  - specialize (IHh1 d2 tl); intuition.
    inversion h3; subst.
    specialize (ast_num_max_decl _ _ _ _ H H5 h4); intros hz1.
    assert (hz2: n1 + 1 <= declaration_astnum d2); intuition.
    specialize (ast_nums_lt_trans0 _ _ _ hz1 hz2); intros hz3.
    specialize (H1 _ _ H7 hz3).
    assumption.
Qed.

(* =============================== *)

(** Functional semantics for expression and statement evaluation 
    with run time checks as passed in parameters; 
*)

Function f_eval_expr_with_checks (ckp: check_points) (s: stack) (e: expression): return_val :=
    match e with
    | E_Literal ast_num l => Val_Normal (eval_literal l)
    | E_Identifier ast_num x => 
        match fetch x s with
        | Some v => Val_Normal v
        | _ => Val_Abnormal
        end
    | E_Binary_Operation ast_num op e1 e2 => 
        match f_eval_expr_with_checks ckp s e1 with
        | Val_Normal v1 => 
            match f_eval_expr_with_checks ckp s e2 with
            | Val_Normal v2 => 
                let cks := fetch_cks ast_num ckp in
                match f_do_flagged_checks cks op v1 v2 with
                | Some true => f_eval_bin_expr op v1 v2
                | Some false => Val_Run_Time_Error
                | _ => Val_Abnormal
                end
            | Val_Run_Time_Error => Val_Run_Time_Error
            | _ => Val_Abnormal
            end
        | Val_Run_Time_Error => Val_Run_Time_Error
        | _ => Val_Abnormal
        end
    | E_Unary_Operation ast_num op e0 =>
        match f_eval_expr_with_checks ckp s e0 with
        | Val_Normal v => f_eval_unary_expr op v
        | Val_Run_Time_Error => Val_Run_Time_Error
        | _ => Val_Abnormal
        end
    end.

Function f_eval_stmt_with_checks k (ckp: check_points) (s: stack) (c: statement): state :=
  match k with
  | 0 => S_Unterminated
  | S k' =>
    match c with
    | S_Assignment ast_num x e =>
        match f_eval_expr_with_checks ckp s e with
        | Val_Normal v => 
            match update s x (Value v) with
            | Some s1 => S_Normal s1
            | _ => S_Abnormal
            end
        | Val_Run_Time_Error => S_Run_Time_Error
        | _ => S_Abnormal
        end
    | S_Sequence ast_num c1 c2 =>
        match f_eval_stmt_with_checks k' ckp s c1 with
        | S_Normal s1 => f_eval_stmt_with_checks k' ckp s1 c2
        | S_Run_Time_Error => S_Run_Time_Error
        | S_Unterminated => S_Unterminated
        | _ => S_Abnormal
        end
    | S_If ast_num b c0 =>
        match f_eval_expr_with_checks ckp s b with
        | Val_Normal (Bool true) => f_eval_stmt_with_checks k' ckp s c0
        | Val_Normal (Bool false) => S_Normal s
        | Val_Run_Time_Error => S_Run_Time_Error
        | _ => S_Abnormal
        end
    | S_While_Loop ast_num b c' =>
        match f_eval_expr_with_checks ckp s b with
        | Val_Normal (Bool true) => 
            match f_eval_stmt_with_checks k' ckp s c' with
            | S_Normal s1 => f_eval_stmt_with_checks k' ckp s1 (S_While_Loop ast_num b c')
            | S_Run_Time_Error => S_Run_Time_Error
            | S_Unterminated => S_Unterminated
            | _ => S_Abnormal
            end
        | Val_Normal (Bool false) => S_Normal s
        | Val_Run_Time_Error => S_Run_Time_Error
        | _ => S_Abnormal
        end
    end
  end.

Function f_eval_decl_with_checks (cps: check_points) (s: stack) (d: object_declaration): state :=
    match d.(initialization_expression) with
    | Some i =>
        match f_eval_expr_with_checks cps s i with
        | Val_Normal v => S_Normal ((d.(object_name), Value v) :: s)
        | Val_Run_Time_Error => S_Run_Time_Error
        | _ => S_Abnormal
        end
    | None => S_Normal ((d.(object_name), Undefined) :: s)
    end.

Function f_eval_decls_with_checks (cps: check_points) (s: stack) (ds: list object_declaration): state :=
    match ds with
    | nil => S_Normal s
    | d :: tl =>
        match f_eval_decl_with_checks cps s d with
        | S_Normal s1 => f_eval_decls_with_checks cps s1 tl
        | S_Run_Time_Error => S_Run_Time_Error
        | _ => S_Abnormal
        end
    end.

Function f_eval_proc_body_with_checks k (cps: check_points) (s: stack) (f: procedure_body): state :=
    match f_eval_decls_with_checks cps s f.(procedure_declarative_part) with
    | S_Normal s1 => f_eval_stmt_with_checks k cps s1 f.(procedure_statements)
    | S_Run_Time_Error => S_Run_Time_Error
    | _ => S_Abnormal
    end.

Function f_eval_subprogram_with_checks k (cps: check_points) (s: stack) (p: subprogram): state :=
    match p with
    | Procedure ast_num f =>
        f_eval_proc_body_with_checks k cps s f
    end.

(* ============================================ *)

(** Semantical equivalence between the relatioinal semantics and 
    functional semantics for program evaluation with checks 
    as passed in parameters; 
*)

Lemma f_eval_expr_with_checks_correct0: forall ckp s e v,
    f_eval_expr_with_checks ckp s e = Val_Normal v ->
    eval_expr_with_checks ckp s e (Val_Normal v).
Proof.
    intros ckp s e;
    functional induction (f_eval_expr_with_checks ckp s e);
    intros v' h1;
    try match goal with
    | [h: Val_Run_Time_Error = Val_Normal ?v |- _] => inversion h
    | [h: Val_Abnormal = Val_Normal ?v |- _] => inversion h
    | [h: Val_Normal ?v1 = Val_Normal ?v2 |- _] => inversion h
    end; subst; auto.
  - constructor.
    reflexivity.
  - constructor.
    assumption.
  - specialize (IHr _ e3).
    specialize (IHr0 _ e4).
    remember (fetch_cks ast_num ckp) as x.
    symmetry in Heqx.
    destruct x.
    + econstructor.
      exact IHr. exact IHr0.
      exact Heqx.
      constructor.
      apply f_eval_bin_expr_correct; auto.
    + econstructor.
      exact IHr. exact IHr0.
      exact Heqx.
      apply f_do_flagged_checks_correct; auto.
      apply f_eval_bin_expr_correct; auto.
  - specialize (IHr _ e2).
    econstructor.
    exact IHr.
    apply f_eval_unary_expr_correct; auto.
Qed.

Lemma f_eval_expr_with_checks_correct1: forall ckp s e,
    f_eval_expr_with_checks ckp s e = Val_Run_Time_Error ->
    eval_expr_with_checks ckp s e Val_Run_Time_Error.
Proof.
    intros ckp s e;
    functional induction (f_eval_expr_with_checks ckp s e);
    intros h1;
    try match goal with
    |[h: Val_Normal ?v = Val_Run_Time_Error |- _] => inversion h
    |[h: Val_Abnormal = Val_Run_Time_Error |- _] => inversion h
    end.
  - destruct v1, v2, op;
    simpl in h1; inversion h1.
  - specialize (f_eval_expr_with_checks_correct0 _ _ _ _ e3); intros hz1.
    specialize (f_eval_expr_with_checks_correct0 _ _ _ _ e4); intros hz2.
    remember (fetch_cks ast_num ckp) as x.
    symmetry in Heqx.
    destruct x.
    * eapply eval_Binary_Operation3.
      apply hz1. apply hz2. apply Heqx.
      apply f_do_flagged_checks_correct; auto.
    * eapply eval_Binary_Operation3.
      apply hz1. apply hz2. apply Heqx.
      apply f_do_flagged_checks_correct; auto.
  - specialize (IHr0 e4).
    eapply eval_Binary_Operation2.
    specialize (f_eval_expr_with_checks_correct0 _ _ _ _ e3); intros hz1.
    apply hz1. assumption.
  - specialize (IHr e3).
    constructor; assumption.
  - destruct op, v; 
    simpl in h1; inversion h1.
  - specialize (IHr e2).
    constructor; auto.
Qed.

Lemma f_eval_expr_with_checks_correct: forall ckp s e v,
    (f_eval_expr_with_checks ckp s e = Val_Normal v ->
        eval_expr_with_checks ckp s e (Val_Normal v)) /\ 
    (f_eval_expr_with_checks ckp s e = Val_Run_Time_Error ->
        eval_expr_with_checks ckp s e Val_Run_Time_Error).
Proof.
    intros.
    split; intros.
  - apply f_eval_expr_with_checks_correct0; 
    auto.
  - apply f_eval_expr_with_checks_correct1; 
    auto.
Qed.

Lemma f_eval_expr_with_checks_complete: forall ckp s e v,
    eval_expr_with_checks ckp s e v ->
    f_eval_expr_with_checks ckp s e = v.
Proof.
    intros ckp s e v h1;
    induction h1;
    simpl;
    repeat match goal with
    | [h: ?x = ?y |- _] => rewrite h; clear h
    end; auto.
  - rewrite (f_do_flagged_checks_complete _ _ _ _ _ H0).
    reflexivity.
  - rewrite (f_do_flagged_checks_complete _ _ _ _ _ H0).
    apply f_eval_bin_expr_complete; auto.
  - apply f_eval_unary_expr_complete; auto.
Qed.

Ltac apply_expr_correct_lemma :=
    match goal with
    | |- eval_expr_with_checks ?ckp ?s ?e (Val_Normal ?v) => 
        apply f_eval_expr_with_checks_correct0
    | |- eval_expr_with_checks ?ckp ?s ?e Val_Run_Time_Error =>
        apply f_eval_expr_with_checks_correct1
    end; auto.

Ltac apply_expr_complete_lemma :=
    match goal with
    | h: eval_expr_with_checks ?ckp ?s ?e ?s' |- _ =>
        rewrite (f_eval_expr_with_checks_complete _ _ _ _ h)
    end; auto.

Lemma f_eval_stmt_with_checks_correct0: forall k ckp s c s',
    f_eval_stmt_with_checks k ckp s c = (S_Normal s') ->
    eval_stmt_with_checks ckp s c (S_Normal s').
Proof.
    intros k ckp s c;
    functional induction (f_eval_stmt_with_checks k ckp s c);
    intros s' h1;
    try match goal with
    | [h: S_Unterminated = S_Normal ?s |- _] => inversion h
    | [h: S_Run_Time_Error = S_Normal ?s |- _] => inversion h
    | [h: S_Abnormal = S_Normal ?s |- _] => inversion h
    | [h: S_Normal ?s1 = S_Normal ?s2 |- _] => inversion h; subst
    end.
  - econstructor. 
    apply_expr_correct_lemma.
    apply e2.
    assumption.
  - specialize (IHs0 _ e1).
    specialize (IHs1 _ h1).
    econstructor.
    apply IHs0. assumption.
  - specialize (IHs0 _ h1).
    econstructor.
    apply_expr_correct_lemma.
    assumption.
  - eapply eval_If_False.
    apply_expr_correct_lemma.
  - specialize (IHs0 _ e2).
    specialize (IHs1 _ h1).
    econstructor.
    apply_expr_correct_lemma.
    apply IHs0. assumption.
  - apply eval_While_Loop_False.
    apply_expr_correct_lemma.
Qed.

Lemma f_eval_stmt_with_checks_correct1: forall k ckp s c,
    f_eval_stmt_with_checks k ckp s c = S_Run_Time_Error ->
    eval_stmt_with_checks ckp s c S_Run_Time_Error.
Proof.
    intros k ckp s c h1;
    functional induction (f_eval_stmt_with_checks k ckp s c);
    try match goal with
    | [h: S_Unterminated = S_Run_Time_Error |- _] => inversion h
    | [h: S_Abnormal = S_Run_Time_Error |- _] => inversion h
    | [h: S_Normal ?s1 = S_Run_Time_Error |- _] => inversion h
    end.
  - constructor.
    apply_expr_correct_lemma.
  - specialize (IHs1 h1).
    specialize (f_eval_stmt_with_checks_correct0 _ _ _ _ _ e1); intros hz1.
    eapply eval_Sequence2.
    apply hz1. assumption.
  - specialize (IHs0 e1).
    econstructor; auto.
  - specialize (IHs0 h1).
    apply eval_If_True.
    apply_expr_correct_lemma.
    assumption.
  - constructor.
    apply_expr_correct_lemma.
  - specialize (IHs1 h1).
    eapply eval_While_Loop_True2.
    apply_expr_correct_lemma.
    specialize (f_eval_stmt_with_checks_correct0 _ _ _ _ _ e2); intros hz1.
    apply hz1.
    assumption.
  - specialize (IHs0 e2).
    eapply eval_While_Loop_True1.
    apply_expr_correct_lemma.
    assumption.
  - constructor.
    apply_expr_correct_lemma.
Qed.

Lemma f_eval_stmt_with_checks_correct: forall k ckp s c s',
    (f_eval_stmt_with_checks k ckp s c = (S_Normal s') ->
        eval_stmt_with_checks ckp s c (S_Normal s')) /\
    (f_eval_stmt_with_checks k ckp s c = S_Run_Time_Error ->
        eval_stmt_with_checks ckp s c S_Run_Time_Error).
Proof.
    intros;
    split; intros h1.
  - apply f_eval_stmt_with_checks_correct0 with (k := k).
    assumption.
  - apply f_eval_stmt_with_checks_correct1 with (k := k).
    assumption.
Qed.

(** Some help lemmas to prove f_eval_stmt_with_checks_complete; *)

Lemma eval_stmt_with_checks_state : forall ckp s c s',
        eval_stmt_with_checks ckp s c s' ->
            (exists v, s' = S_Normal v) \/ s' = S_Run_Time_Error.
Proof.
    intros ckp s c s' h.
    induction h;
    try match goal with
    | [ |- (exists v', S_Normal ?v = S_Normal v') \/ _ ] => left; exists v; reflexivity
    | [ |- context [ _ \/ ?A = ?A ] ] => right; reflexivity
    end; auto.
Qed.

Ltac apply_inv1 :=
  match goal with
    | H:S_Unterminated = S_Normal _ |- _ => inversion H
    | H:S_Unterminated = S_Run_Time_Error |- _ => inversion H
    | H:S_Unterminated = S_Abnormal |- _ => inversion H
    | H:S_Abnormal = S_Normal _ |- _ => inversion H
    | H:S_Abnormal = S_Run_Time_Error |- _ => inversion H
    | H:S_Abnormal = S_Unterminated |- _ => inversion H
    | H:S_Run_Time_Error = S_Normal _ |- _ => inversion H
    | H:S_Run_Time_Error = S_Abnormal |- _ => inversion H
    | H:S_Run_Time_Error = S_Unterminated |- _ => inversion H
    | H:S_Normal _ = S_Unterminated |- _ => inversion H
    | H:S_Normal _ = S_Run_Time_Error |- _ => inversion H
    | H:S_Normal _ = S_Abnormal |- _ => inversion H
    | H:S_Normal _ = S_Normal _ |- _ => inversion H;clear H;subst 
    | H:update _ _ (Value _) = _ |- _ => rewrite H
    | H:f_eval_expr_with_checks _ _ _ = _ |- _ => rewrite H
    | H:f_eval_expr_with_checks _ _ = _ |- _ => rewrite H
    | H: f_eval_stmt_with_checks _ _ _ _ = _ |- _ => rewrite H
  end;subst;simpl;auto.

Lemma f_eval_stmt_with_checks_fixpoint: forall k ckp s c s', 
        f_eval_stmt_with_checks k ckp s c = S_Normal s' ->
        forall k':nat, (k <= k')%nat -> 
            f_eval_stmt_with_checks k' ckp s c = S_Normal s'.
Proof.
    intros k ckp s c.
    functional induction (f_eval_stmt_with_checks k ckp s c); simpl; intros; subst; simpl; auto;
    repeat progress apply_inv1.
  - invle; 
    repeat apply_inv1.
  - invle.
    + repeat apply_inv1.
    + rewrite (IHs0 _ e1);auto with arith.
  - invle; repeat apply_inv1. rewrite (IHs0 _ H);auto with arith.
  - invle; repeat apply_inv1.
  - invle; repeat apply_inv1. rewrite (IHs0 _ e2); auto with arith.
  - invle; repeat apply_inv1.
Qed.

Lemma f_eval_stmt_with_checks_fixpoint_E: forall k ckp s c, 
        f_eval_stmt_with_checks k ckp s c = S_Run_Time_Error ->
        forall k':nat, (k <= k')%nat -> 
            f_eval_stmt_with_checks k' ckp s c = S_Run_Time_Error.
Proof.
    intros k ckp s c.
    functional induction (f_eval_stmt_with_checks k ckp s c); simpl; intros; subst; simpl; auto;
    repeat progress apply_inv1.
  - invle;
    apply_inv1.
  - invle;
    repeat apply_inv1.
    rewrite (f_eval_stmt_with_checks_fixpoint _ _ _ _ _ e1); auto with arith.
  - invle;
    repeat apply_inv1.
    specialize (IHs0 e1). 
    rewrite IHs0; auto with arith. 
  - invle; 
    repeat apply_inv1.
    rewrite IHs0; auto with arith.
  - invle;
    repeat apply_inv1.
  - invle; 
    repeat apply_inv1. 
    rewrite (f_eval_stmt_with_checks_fixpoint _ _ _ _ _ e2); auto with arith.
  - invle; 
    repeat apply_inv1.
    rewrite (IHs0 e2); auto with arith.
  - invle; 
    repeat apply_inv1.
Qed.

Ltac kgreater1 :=
  repeat match goal with
           | h:f_eval_stmt_with_checks ?k ?ckp ?s ?c = S_Normal ?s' |- context [f_eval_stmt_with_checks (?k + _) ?ckp ?s ?c] =>
             rewrite (@f_eval_stmt_with_checks_fixpoint _ _ _ _ _ h);auto with arith
           | h:f_eval_stmt_with_checks ?k ?ckp ?s ?c = S_Normal ?s' |- context [f_eval_stmt_with_checks (_ + ?k) ?ckp ?s ?c] =>
             rewrite (@f_eval_stmt_with_checks_fixpoint _ _ _ _ _ h);auto with arith
           | h:f_eval_stmt_with_checks ?k ?ckp ?s ?c = S_Run_Time_Error |- context [f_eval_stmt_with_checks (?k + _) ?ckp ?s ?c] =>
             rewrite (@f_eval_stmt_with_checks_fixpoint_E _ _ _ _ h);auto with arith
           | h:f_eval_stmt_with_checks ?k ?ckp ?s ?c = S_Run_Time_Error |- context [f_eval_stmt_with_checks (_ + ?k) ?ckp ?s ?c] =>
             rewrite (@f_eval_stmt_with_checks_fixpoint_E _ _ _ _ h);auto with arith
         end.

Ltac apply_rewrite1 := 
    match goal with
    | h: eval_expr_with_checks ?ckp ?s ?b ?s' |- _ => 
        rewrite (f_eval_expr_with_checks_complete _ _ _ _ h)
    | h: update _ _ _ = _ |- _ => rewrite h
    end; auto.


Lemma f_eval_stmt_with_checks_complete: forall ckp s c s',
    eval_stmt_with_checks ckp s c s' ->
    exists k, f_eval_stmt_with_checks k ckp s c = s'.
Proof.
    intros ckp s c s' h1;
    induction h1.
    (* 1. Sassign *)
  - exists 1; simpl.
    apply_rewrite1.
  - exists 1; simpl.
    repeat apply_rewrite1.
    (* 2. Sseq *)
  - destrIH.
    exists (S k); simpl.
    apply_inv1.
  - destrIH.
    exists (S (k0 + k)); simpl.
    kgreater1.
    specialize (eval_stmt_with_checks_state _ _ _ _ h1_2); intros hz1.
    destruct hz1 as [hz2 | hz2].
    + destrIH; rewrite hk1 in *; kgreater1.
    + rewrite hz2 in *; kgreater1.
  (* 3. Sifthen *)
  - exists 1%nat; simpl.
    apply_rewrite1.
  - destrIH.
    exists (S k); simpl.
    apply_rewrite1.
  (* 4. Swhile *)
  - exists 1%nat; simpl.
    apply_rewrite1.
  - exists 1%nat; simpl.
    apply_rewrite1.
  - destrIH.
    exists (S k); simpl.
    apply_rewrite1.
    apply_inv1.
  - destrIH.
    exists (S (k0+k)); simpl.
    apply_rewrite1.
    kgreater1.
    specialize (eval_stmt_with_checks_state _ _ _ _ h1_2); intros hz1.
    destruct hz1 as [hz2 | hz2].
    + destrIH; rewrite hk1 in *; kgreater1.
    + rewrite hz2 in *; kgreater1.
  - exists 1%nat; simpl.
    apply_rewrite1.
Qed.

Lemma f_eval_decl_with_checks_correct0: forall ckp s d s',
    f_eval_decl_with_checks ckp s d = S_Normal s' ->
       eval_decl_with_checks ckp s d (S_Normal s').
Proof.
    intros ckp s d;
    functional induction (f_eval_decl_with_checks ckp s d);
    intros s' h1;
    try match goal with
    | h: S_Abnormal = S_Normal ?s |- _ => inversion h
    | h: S_Run_Time_Error = S_Normal ?s |- _ => inversion h
    | h: S_Normal ?s1 = S_Normal ?s2 |- _ => inversion h; subst
    end; auto.
  - econstructor; auto.
    symmetry in e; apply e.
    apply_expr_correct_lemma.
  - econstructor; intuition.
Qed.

Lemma f_eval_decl_with_checks_correct1: forall ckp s d,
    f_eval_decl_with_checks ckp s d = S_Run_Time_Error ->
       eval_decl_with_checks ckp s d S_Run_Time_Error.
Proof.
    intros ckp s d;
    functional induction (f_eval_decl_with_checks ckp s d);
    intros h1;
    try match goal with
    | h: S_Abnormal = S_Run_Time_Error |- _ => inversion h
    | h: S_Normal ?s = S_Run_Time_Error |- _ => inversion h
    end; auto.
    econstructor.
    symmetry in e; apply e.
    apply_expr_correct_lemma.
Qed.

Lemma f_eval_decl_with_checks_correct: forall ckp s d s',
    (f_eval_decl_with_checks ckp s d = S_Normal s' ->
       eval_decl_with_checks ckp s d (S_Normal s')) /\
    (f_eval_decl_with_checks ckp s d = S_Run_Time_Error ->
       eval_decl_with_checks ckp s d S_Run_Time_Error).
Proof.
    intros ckp s d s';
    split; intros h1.
  - apply f_eval_decl_with_checks_correct0; auto.
  - apply f_eval_decl_with_checks_correct1; auto.
Qed.

Lemma f_eval_decl_with_checks_complete: forall ckp s d s',
    eval_decl_with_checks ckp s d s' ->
    f_eval_decl_with_checks ckp s d = s'.
Proof.
    intros ckp s d s' h1;
    induction h1;
    unfold f_eval_decl_with_checks;
    rewrite <- H; try rewrite <- H0;
    auto.
  - apply_expr_complete_lemma.
  - apply_expr_complete_lemma.
Qed.

Ltac apply_decl_correct_lemma :=
    match goal with
    | |- eval_decl_with_checks ?ckp ?s ?d (S_Normal ?s') => apply f_eval_decl_with_checks_correct0
    | |- eval_decl_with_checks ?ckp ?s ?d S_Run_Time_Error => apply f_eval_decl_with_checks_correct1
    end; auto.

Ltac apply_decl_complete_lemma :=
    match goal with
    | h: eval_decl_with_checks ?ckp ?s ?d ?s' |- _ => apply f_eval_decl_with_checks_complete
    end; auto.

Lemma f_eval_decls_with_checks_correct0: forall ckp s ds s',
    f_eval_decls_with_checks ckp s ds = S_Normal s' ->
        eval_decls_with_checks ckp s ds (S_Normal s').
Proof.
    intros ckp s ds; 
    functional induction (f_eval_decls_with_checks ckp s ds);
    intros s' h1;
    try match goal with
    | h: S_Abnormal = S_Normal ?s |- _ => inversion h
    | h: S_Run_Time_Error = S_Normal ?s |- _ => inversion h
    | h: S_Normal ?s1 = S_Normal ?s2 |- _ => inversion h; subst
    end; auto.
  - constructor.
  - specialize (IHs0 _ h1).
    econstructor.
    apply_decl_correct_lemma. apply e0.
    assumption.
Qed.

Lemma f_eval_decls_with_checks_correct1: forall ckp s ds,
    f_eval_decls_with_checks ckp s ds = S_Run_Time_Error ->
        eval_decls_with_checks ckp s ds S_Run_Time_Error.
Proof.
    intros ckp s ds;
    functional induction (f_eval_decls_with_checks ckp s ds);
    intros h1;
    try match goal with
    | h: S_Abnormal = S_Run_Time_Error |- _ => inversion h
    | h: S_Normal ?s = S_Run_Time_Error |- _ => inversion h
    end; auto.
  - specialize (IHs0 h1).
    eapply eval_Decls1.
    apply_decl_correct_lemma. apply e0.
    assumption.
  - constructor.
    apply_decl_correct_lemma.
Qed.

Lemma f_eval_decls_with_checks_correct: forall ckp s ds s',
    (f_eval_decls_with_checks ckp s ds = S_Normal s' ->
        eval_decls_with_checks ckp s ds (S_Normal s')) /\
    (f_eval_decls_with_checks ckp s ds = S_Run_Time_Error ->
        eval_decls_with_checks ckp s ds S_Run_Time_Error).
Proof.
    intros;
    split; intros h1.
  - apply f_eval_decls_with_checks_correct0.
    assumption.
  - apply f_eval_decls_with_checks_correct1.
    assumption.
Qed.

Lemma f_eval_decls_with_checks_complete: forall ckp s ds s',
    eval_decls_with_checks ckp s ds s' ->
    f_eval_decls_with_checks ckp s ds = s'.
Proof.
    intros ckp s ds s' h1.
    induction h1;
    simpl; auto.
  - rewrite (f_eval_decl_with_checks_complete _ _ _ _ H).
    reflexivity.
  - rewrite (f_eval_decl_with_checks_complete _ _ _ _ H).
    assumption.
Qed.

Lemma f_eval_proc_body_with_checks_correct0: forall k ckp s f s',
    f_eval_proc_body_with_checks k ckp s f = S_Normal s' ->
        eval_proc_body_with_checks ckp s f (S_Normal s').
Proof.
    intros k ckp s f;
    functional induction (f_eval_proc_body_with_checks k ckp s f);
    intros s' h1;
    try match goal with
    |h: S_Run_Time_Error = S_Normal ?s |- _ => inversion h
    |h: S_Abnormal = S_Normal ?s |- _ => inversion h
    end.
  - econstructor.
    apply f_eval_decls_with_checks_correct0.
    apply e.
    apply f_eval_stmt_with_checks_correct0 with (k := k).
    assumption.
Qed.

Lemma f_eval_proc_body_with_checks_correct1: forall k ckp s f,
    f_eval_proc_body_with_checks k ckp s f = S_Run_Time_Error ->
        eval_proc_body_with_checks ckp s f S_Run_Time_Error.
Proof.
    intros k ckp s f;
    functional induction (f_eval_proc_body_with_checks k ckp s f);
    intros h1;
    try match goal with
    |h: S_Normal ?s = S_Run_Time_Error |- _ => inversion h
    |h: S_Abnormal = S_Run_Time_Error |- _ => inversion h
    end.
  - eapply eval_Proc_Body1.
    apply f_eval_decls_with_checks_correct0. 
    apply e.
    apply f_eval_stmt_with_checks_correct1 with (k := k).
    assumption.
  - constructor.
    apply f_eval_decls_with_checks_correct1.
    assumption.
Qed.

Lemma f_eval_proc_body_with_checks_correct: forall k ckp s f s',
    (f_eval_proc_body_with_checks k ckp s f = S_Normal s' ->
        eval_proc_body_with_checks ckp s f (S_Normal s')) /\
    (f_eval_proc_body_with_checks k ckp s f = S_Run_Time_Error ->
        eval_proc_body_with_checks ckp s f S_Run_Time_Error).
Proof.
    intros;
    split; intros h1.
  - apply f_eval_proc_body_with_checks_correct0 with (k := k).
    assumption.
  - apply f_eval_proc_body_with_checks_correct1 with (k := k).
    assumption.
Qed.

Lemma f_eval_proc_body_with_checks_complete: forall ckp s f s',
    eval_proc_body_with_checks ckp s f s' ->
    exists k, f_eval_proc_body_with_checks k ckp s f = s'.
Proof.
    intros ckp s f s' h1;
    induction h1;
    unfold f_eval_proc_body_with_checks.
  - rewrite (f_eval_decls_with_checks_complete _ _ _ _ H).
    exists 1%nat.
    reflexivity.
  - rewrite (f_eval_decls_with_checks_complete _ _ _ _ H).
    apply f_eval_stmt_with_checks_complete.
    assumption.
Qed.

Lemma f_eval_subprogram_with_checks_correct0: forall k ckp s p s',
    f_eval_subprogram_with_checks k ckp s p = S_Normal s' ->
        eval_subprogram_with_checks ckp s p (S_Normal s').
Proof.
    intros k ckp s p;
    functional induction (f_eval_subprogram_with_checks k ckp s p);
    intros s' h1.
  - constructor.
    apply f_eval_proc_body_with_checks_correct0 with (k := k);
    auto.
Qed.

Lemma f_eval_subprogram_with_checks_correct1: forall k ckp s p,
    f_eval_subprogram_with_checks k ckp s p = S_Run_Time_Error ->
        eval_subprogram_with_checks ckp s p S_Run_Time_Error.
Proof.
    intros k ckp s p;
    functional induction (f_eval_subprogram_with_checks k ckp s p);
    intros h1.
  - constructor.
    apply f_eval_proc_body_with_checks_correct1 with (k := k);
    auto.
Qed.

Lemma f_eval_subprogram_with_checks_correct: forall k ckp s p s',
    (f_eval_subprogram_with_checks k ckp s p = S_Normal s' ->
        eval_subprogram_with_checks ckp s p (S_Normal s')) /\
    (f_eval_subprogram_with_checks k ckp s p = S_Run_Time_Error ->
        eval_subprogram_with_checks ckp s p S_Run_Time_Error).
Proof.
    intros;
    split; intros h1.
  - apply f_eval_subprogram_with_checks_correct0 with (k := k);
    auto.
  - apply f_eval_subprogram_with_checks_correct1 with (k := k);
    auto.
Qed.

Lemma f_eval_subprogram_with_checks_complete: forall ckp s p s',
    eval_subprogram_with_checks ckp s p s' ->
    exists k, f_eval_subprogram_with_checks k ckp s p = s'.
Proof.
    intros ckp s p s' h1;
    induction h1.
  - specialize (f_eval_proc_body_with_checks_complete _ _ _ _ H); intros hz1.
    destrIH.
    exists k; unfold f_eval_subprogram_with_checks.
    assumption.
Qed.


