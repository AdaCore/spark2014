Require Export language.
Require Export language_flagged.
Require Export environment.

Definition level := nat.

(****************************************

   Symbol Table for Unflagged Semantics

 ****************************************)

(* each procedure declaration is associated with a scope level, 
   which can be used to determine what variables are visible to 
   the procedure when it's called;
*)

Record symboltable := mkSymbolTable{
  vars:   list (idnum * (mode * type));
  procs: list (procnum * (level * procedure_declaration));
  types:  list (typenum * type_declaration)
}.

Module Entry_Type <: ENTRY.

  Definition T := prod mode type.

End Entry_Type.

Module Entry_Procedure_Decl <: ENTRY.

  Definition T := prod level procedure_declaration.

End Entry_Procedure_Decl.

Module Entry_Type_Decl <: ENTRY.

  Definition T := type_declaration.

End Entry_Type_Decl.

Module SymTable_Vars  := STORE(Entry_Type).
Module SymTable_Procs := STORE(Entry_Procedure_Decl).
Module SymTable_Types := STORE(Entry_Type_Decl).

Function reside_symtable_vars (x: idnum)   (st: symboltable) := SymTable_Vars.resides x st.(vars).
Function reside_symtable_procs (x: procnum) (st: symboltable) := SymTable_Procs.resides x st.(procs).
Function reside_symtable_types (x: typenum) (st: symboltable) := SymTable_Types.resides x st.(types).

Function fetch_var  (x: idnum)   (st: symboltable) := SymTable_Vars.fetches x st.(vars).
Function fetch_proc (x: procnum) (st: symboltable) := SymTable_Procs.fetches x st.(procs).
Function fetch_type (x: typenum) (st: symboltable) := SymTable_Types.fetches x st.(types).  

Function update_store {V} (s: list (idnum * V)) (i: idnum) (v: V): list (idnum * V) :=
  match s with 
  | (i1, v1) :: s1 =>
      if beq_nat i1 i then
        (i1, v) :: s1
      else
        (i1, v1) :: (update_store s1 i v)
  | nil => (i, v) :: nil
  end.

Arguments update_store {V} _ _ _.

Function update_vars (st: symboltable) (x: idnum) (mt: mode * type): symboltable :=
  mkSymbolTable (update_store st.(vars) x mt) st.(procs) st.(types).

Function update_procs (st: symboltable) (pid: procnum) (p: level * procedure_declaration): symboltable :=
  mkSymbolTable st.(vars) (update_store st.(procs) pid p) st.(types).

Function update_types (st: symboltable) (tid: typenum) (td: type_declaration): symboltable :=
  mkSymbolTable st.(vars) st.(procs) (update_store st.(types) tid td).



(****************************************

    Symbol Table for Flagged Semantics

 ****************************************)

Record symboltable_x := mkSymbolTable_x{
  vars_x:   list (idnum * (mode * type));
  procs_x: list (procnum * (level * procedure_declaration_x));
  types_x:  list (typenum * type_declaration_x)
}.


Module Entry_Procedure_Decl_X <: ENTRY.

  Definition T := prod level procedure_declaration_x.

End Entry_Procedure_Decl_X.

Module Entry_Type_Decl_X <: ENTRY.

  Definition T := type_declaration_x.

End Entry_Type_Decl_X.

Module SymTable_Vars_X  := STORE(Entry_Type).
Module SymTable_Procs_X := STORE(Entry_Procedure_Decl_X).
Module SymTable_Types_X := STORE(Entry_Type_Decl_X).

Function reside_symtable_vars_x (x: idnum)   (st: symboltable_x) := SymTable_Vars_X.resides x st.(vars_x).
Function reside_symtable_procs_x (x: procnum) (st: symboltable_x) := SymTable_Procs_X.resides x st.(procs_x).
Function reside_symtable_types_x (x: typenum) (st: symboltable_x) := SymTable_Types_X.resides x st.(types_x).

Function fetch_var_x  (x: idnum)   (st: symboltable_x) := SymTable_Vars_X.fetches x st.(vars_x).
Function fetch_proc_x (x: procnum) (st: symboltable_x) := SymTable_Procs_X.fetches x st.(procs_x).
Function fetch_type_x (x: typenum) (st: symboltable_x) := SymTable_Types_X.fetches x st.(types_x).  

Function update_vars_x (st: symboltable_x) (x: idnum) (mt: mode * type): symboltable_x :=
  mkSymbolTable_x (update_store st.(vars_x) x mt) st.(procs_x) st.(types_x).

Function update_procs_x (st: symboltable_x) (pid: procnum) (p: level * procedure_declaration_x): symboltable_x :=
  mkSymbolTable_x st.(vars_x) (update_store st.(procs_x) pid p) st.(types_x).

Function update_types_x (st: symboltable_x) (tid: typenum) (td: type_declaration_x): symboltable_x :=
  mkSymbolTable_x st.(vars_x) st.(procs_x) (update_store st.(types_x) tid td).




(* **********************************
   build symbol table from SPARK AST 
   ********************************** *)


(*
Inductive symboltable_decl: symboltable -> context -> declaration -> symboltable -> Prop :=

.

Inductive symboltable_subprogram: symboltable -> context -> subprogram -> symboltable
  | ST_Procedure: 
       
      symboltable_subprogram st1 (Global_Procedure ast_num pd) st2.

*)










































