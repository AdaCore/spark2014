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
(* TODO: modify it later *)
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














