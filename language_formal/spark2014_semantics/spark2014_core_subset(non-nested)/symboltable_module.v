Require Export environment.

(** * Symbol Table Elements *)

Module Type SymTable_Element.

  Parameter Procedure_Decl: Type.

  Parameter Type_Decl: Type.
  
  Parameter Source_Location: Type.

End SymTable_Element.

(** * Symbol Table Module *)

Module SymbolTableM (S: SymTable_Element).

  Definition level := nat.
  
  Definition proc_decl := S.Procedure_Decl.

  Definition type_decl := S.Type_Decl.

  Definition source_location := S.Source_Location.
  
  (** ** Symbol Table Structure *)

  Record symboltable := mkSymbolTable{
    vars:   list (idnum * (mode * type));
    procs: list (procnum * (level * proc_decl));
    types:  list (typenum * type_decl);
    exps: list (astnum * type);
    sloc: list (astnum * source_location)
    (*used to map back to the source location once an error is detected in ast tree*)
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

  Module Entry_Exp_Type <: ENTRY.
    Definition T := type.
  End Entry_Exp_Type.

  Module Entry_Sloc <: ENTRY.
    Definition T := source_location.
  End Entry_Sloc.


  Module SymTable_Vars  := STORE(Entry_Type).
  Module SymTable_Procs := STORE(Entry_Procedure_Decl).
  Module SymTable_Types := STORE(Entry_Type_Decl).
  Module SymTable_Exps := STORE(Entry_Exp_Type).
  Module SymTable_Sloc := STORE(Entry_Sloc).

  (** ** Symbol Table Operations *)

  Function reside_symtable_vars (x: idnum)   (st: symboltable) := SymTable_Vars.resides x st.(vars).
  Function reside_symtable_procs (x: procnum) (st: symboltable) := SymTable_Procs.resides x st.(procs).
  Function reside_symtable_types (x: typenum) (st: symboltable) := SymTable_Types.resides x st.(types).
  Function reside_symtable_exps (x: astnum) (st: symboltable) := SymTable_Exps.resides x st.(exps).
  Function reside_symtable_sloc (x: astnum) (st: symboltable) := SymTable_Sloc.resides x st.(sloc).

  Function fetch_var  (x: idnum)   (st: symboltable) := SymTable_Vars.fetches x st.(vars).
  Function fetch_proc (x: procnum) (st: symboltable) := SymTable_Procs.fetches x st.(procs).
  Function fetch_type (x: typenum) (st: symboltable) := SymTable_Types.fetches x st.(types).
  Function fetch_exp_type (x: astnum) (st: symboltable) := SymTable_Exps.fetches x st.(exps).
  Function fetch_sloc (x: astnum) (st: symboltable) := SymTable_Sloc.fetches x st.(sloc).

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
    mkSymbolTable (update_store st.(vars) x mt) st.(procs) st.(types) st.(exps) st.(sloc).

  Function update_procs (st: symboltable) (pid: procnum) (p: level * proc_decl): symboltable :=
    mkSymbolTable st.(vars) (update_store st.(procs) pid p) st.(types) st.(exps) st.(sloc).

  Function update_types (st: symboltable) (tid: typenum) (td: type_decl): symboltable :=
    mkSymbolTable st.(vars) st.(procs) (update_store st.(types) tid td) st.(exps) st.(sloc).

  Function update_exps (st: symboltable) (ast_num: astnum) (t: type): symboltable :=
    mkSymbolTable st.(vars) st.(procs) st.(types) (update_store st.(exps) ast_num t) st.(sloc).

  Function update_sloc (st: symboltable) (ast_num: astnum) (sl: source_location): symboltable :=
    mkSymbolTable st.(vars) st.(procs) st.(types) st.(exps) (update_store st.(sloc) ast_num sl).

End SymbolTableM.











































