Require Export language.
Require Export language_flagged.
Require Export environment.

Module Type SymTable_Element.

  Parameter Procedure_Decl: Type.

  Parameter Type_Decl: Type.

End SymTable_Element.


Module SymbolTableM (S: SymTable_Element).

  Definition level := nat.
  
  Definition proc_decl := S.Procedure_Decl.

  Definition type_decl := S.Type_Decl.
  
  Record symboltable := mkSymbolTable{
    vars:   list (idnum * (mode * type));
    procs: list (procnum * (level * proc_decl));
    types:  list (typenum * type_decl)
  }.

  Module Entry_Type <: ENTRY.
    Definition T := prod mode type.
  End Entry_Type.

  Module Entry_Procedure_Decl <: ENTRY.
    Definition T := prod level proc_decl.
  End Entry_Procedure_Decl.

  Module Entry_Type_Decl <: ENTRY.
    Definition T := type_decl.
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

  Function update_procs (st: symboltable) (pid: procnum) (p: level * proc_decl): symboltable :=
    mkSymbolTable st.(vars) (update_store st.(procs) pid p) st.(types).

  Function update_types (st: symboltable) (tid: typenum) (td: type_decl): symboltable :=
    mkSymbolTable st.(vars) st.(procs) (update_store st.(types) tid td).

End SymbolTableM.


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










































