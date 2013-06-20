(*
   Before executing the program, make sure that the program is well-formed
   - well-typed: 
         * all operators work on the operands of the right types;
         * all assignments write into memory with the values of right types;
   - defined-before-used: all variables are defined (and initialized ? ) before they are used

    index /-----------------------------
              |- well-typed program
              | -----------------------------
              |- well-defined program
              | -----------------------------
*)
Require Export language.
Require Export semantics. 

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

(* well typed 
   1. general typing checking;
   2. all variables should be in mode 'in';
*)
Inductive well_typed_expr: symtb -> expr -> typ -> Prop :=
    | WT_Econst_Int: forall ast_id n tb,
        well_typed_expr tb (Econst ast_id (Ointconst n)) Tint
    | WT_Econst_Bool: forall ast_id b tb,
        well_typed_expr tb (Econst ast_id (Oboolconst b)) Tbool
    | WT_Evar: forall ast_id x tb t,
        Some (In, t) = lookup x tb ->  (* the 'out' variables can never be read *)    
        well_typed_expr tb (Evar ast_id x) t
    | WT_Ebinop: forall ast_id tb op e1 e2 t t1,
        well_typed_expr tb e1 t ->
        well_typed_expr tb e2 t ->
        Some t1 = binop_type op t t ->
        well_typed_expr tb (Ebinop ast_id op e1 e2) t1
    | WT_Eunop: forall ast_id tb op e,
        well_typed_expr tb e Tbool ->
        well_typed_expr tb (Eunop ast_id op e) Tbool.

(* two kinds of type checking:
   1. general type checking;
   2. in / out mode checking;
 *)
Inductive well_typed_stmt: symtb -> stmt  -> Prop :=
    | WT_Sassign: forall ast_id tb x e t,
        Some (Out, t) = lookup x tb ->
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

(* all refered variables are defined *)
Inductive well_defined_expr: stack -> expr -> Prop :=
    | WD_Econst_Int: forall ast_id s n,
        well_defined_expr s (Econst ast_id (Ointconst n))
    | WD_Econst_Bool: forall ast_id s b,
        well_defined_expr s (Econst ast_id (Oboolconst b))
    | WD_Evar: forall ast_id x v s,
        Some v = fetch x s ->
        well_defined_expr s (Evar ast_id x)
    | WD_Ebinop: forall ast_id s op e1 e2,
        well_defined_expr s e1 ->
        well_defined_expr s e2 ->
        well_defined_expr s (Ebinop ast_id op e1 e2)
    | WD_Eunop: forall ast_id s op e,
        well_defined_expr s e ->
        well_defined_expr s (Eunop ast_id op e). 

(* A simple version of well-defined commands *)
(* 
Inductive well_defined_stmt: stack -> stmt -> Prop :=
    | WD_Sassign: forall ast_id s x e,
        reside x s = true ->
        well_defined_expr s e ->
        well_defined_stmt s ((Sassign ast_id x e))
    | WD_Sseq: forall ast_id c1 c2 s,
        well_defined_stmt s c1 ->
        well_defined_stmt s c2 ->
        well_defined_stmt s (Sseq ast_id c1 c2)
    | WD_Sifthen: forall ast_id s b c,
        well_defined_expr s b ->
        well_defined_stmt s c ->
        well_defined_stmt s (Sifthen ast_id b c)
    | WD_Swhile: forall ast_id s b c,
        well_defined_expr s b ->
        well_defined_stmt s c ->
        well_defined_stmt s (Swhile ast_id b c).
(*    | WD_Sassert: forall ast_id s e, 
        well_defined_expr s e ->
        well_defined_stmt s (Sassert ast_id e) *)
*)

(* =============================== *)

Inductive init_mode: Type := 
    | Init: init_mode
    |Uninit: init_mode.

Definition initializationState: Type := list (idnum * init_mode).

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

Inductive well_defined_expr2: initializationState -> expr -> Prop :=
    | WD_Econst_Int2: forall ast_id s n,
        well_defined_expr2 s (Econst ast_id (Ointconst n))
    | WD_Econst_Bool2: forall ast_id s b,
        well_defined_expr2 s (Econst ast_id (Oboolconst b))
    | WD_Evar2: forall ast_id x s,
        Some Init = fetch2 x s ->
        well_defined_expr2 s (Evar ast_id x)
    | WD_Ebinop2: forall ast_id s op e1 e2,
        well_defined_expr2 s e1 ->
        well_defined_expr2 s e2 ->
        well_defined_expr2 s (Ebinop ast_id op e1 e2)
    | WD_Eunop2: forall ast_id s op e,
        well_defined_expr2 s e ->
        well_defined_expr2 s (Eunop ast_id op e). 

Inductive well_defined_stmt2: initializationState -> stmt -> initializationState -> Prop :=
    | WD_Sassign2: forall ast_id s s' x e,
        well_defined_expr2 s e ->
        Some s' = update2 s x Init ->
        well_defined_stmt2 s (Sassign ast_id x e) s'
    | WD_Sseq2: forall ast_id c1 c2 s s' s'',
        well_defined_stmt2 s c1 s' ->
        well_defined_stmt2 s' c2 s'' ->
        well_defined_stmt2 s (Sseq ast_id c1 c2) s''
    | WD_Sifthen2: forall ast_id s s' b c,
        well_defined_expr2 s b ->
        well_defined_stmt2 s c s' ->
        well_defined_stmt2 s (Sifthen ast_id b c) s
    | WD_Swhile2: forall ast_id s s' b c,
        well_defined_expr2 s b ->
        well_defined_stmt2 s c s' ->
        well_defined_stmt2 s (Swhile ast_id b c) s.

(* =============================== *)
(*  - - - Experiment - - -  *)
Function free_vars (e: expr): list idnum :=
    match e with
    | Econst _ _ => nil
    | Evar _ x => x::nil
    | Ebinop _ op e1 e2 =>
        let l1 := free_vars e1 in
        let l2 := free_vars e2 in
        l1 ++ l2
    | Eunop _ op e1 =>
        free_vars e1
    end.

Inductive well_defined_stmt1: stack -> (list idnum)  -> (list idnum) -> stmt -> Prop :=
    | WD_Sassign1: forall ast_id s l l' x e fv,
        fv = free_vars e ->
        (forall x, List.In x fv -> exists v, Some v = fetch x s \/ List.In x l) -> 
        l' = x::l ->
        well_defined_stmt1 s l l' ((Sassign ast_id x e))
    | WD_Sseq1: forall ast_id c1 c2 s l l' l'',
        well_defined_stmt1 s l l' c1 ->
        well_defined_stmt1 s l' l'' c2 ->
        well_defined_stmt1 s l l'' (Sseq ast_id c1 c2)
    | WD_Sifthen1: forall ast_id s b c l l' fv,
        fv = free_vars b -> 
        (forall x, List.In x fv -> exists v, Some v = fetch x s \/ List.In x l) ->
        well_defined_expr s b ->
        well_defined_stmt1 s l l' c ->
        well_defined_stmt1 s l l (Sifthen ast_id b c)
    | WD_Swhile1: forall ast_id s b c l l' fv,
        fv = free_vars b -> 
        (forall x, List.In x fv -> exists v, Some v = fetch x s \/ List.In x l) ->
        well_defined_stmt1 s l l' c ->
        well_defined_stmt1 s l l (Swhile ast_id b c).














