Require Export symboltable_module.
Require Export language_flagged.

(** * Symbol Tables *)

(* symbol table for unflagged program *)
Module Symbol_Table_Elements <: SymTable_Element.
  Definition Procedure_Decl := procedure_body.
  Definition Type_Decl := type_declaration.
End Symbol_Table_Elements.

(* symbol table for flagged program *)
Module Symbol_Table_Elements_X <: SymTable_Element.
  Definition Procedure_Decl := procedure_body_x.
  Definition Type_Decl := type_declaration_x.
End Symbol_Table_Elements_X.

Module Symbol_Table_Module := SymbolTableM (Symbol_Table_Elements).

Module Symbol_Table_Module_X := SymbolTableM (Symbol_Table_Elements_X).

Definition symboltable := Symbol_Table_Module.symboltable.
Definition mkSymbolTable := Symbol_Table_Module.mkSymbolTable.
Definition proc_decl := Symbol_Table_Module.proc_decl.
Definition type_decl := Symbol_Table_Module.type_decl.

Definition symboltable_x := Symbol_Table_Module_X.symboltable.
Definition mkSymbolTable_x := Symbol_Table_Module_X.mkSymbolTable.
Definition proc_decl_x := Symbol_Table_Module_X.proc_decl.
Definition type_decl_x := Symbol_Table_Module_X.type_decl.

Definition level := Symbol_Table_Module.level.

Definition reside_symtable_vars := Symbol_Table_Module.reside_symtable_vars.
Definition reside_symtable_procs := Symbol_Table_Module.reside_symtable_procs.
Definition reside_symtable_types := Symbol_Table_Module.reside_symtable_types.
Definition reside_symtable_exps := Symbol_Table_Module.reside_symtable_exps.
Definition fetch_var := Symbol_Table_Module.fetch_var.
Definition fetch_proc := Symbol_Table_Module.fetch_proc.
Definition fetch_type := Symbol_Table_Module.fetch_type.
Definition fetch_exp_type := Symbol_Table_Module.fetch_exp_type.
Definition update_vars := Symbol_Table_Module.update_vars.
Definition update_procs := Symbol_Table_Module.update_procs.
Definition update_types := Symbol_Table_Module.update_types.
Definition update_exps := Symbol_Table_Module.update_exps.

Definition reside_symtable_vars_x := Symbol_Table_Module_X.reside_symtable_vars.
Definition reside_symtable_procs_x := Symbol_Table_Module_X.reside_symtable_procs.
Definition reside_symtable_types_x := Symbol_Table_Module_X.reside_symtable_types.
Definition reside_symtable_exps_x := Symbol_Table_Module_X.reside_symtable_exps.
Definition fetch_var_x := Symbol_Table_Module_X.fetch_var.
Definition fetch_proc_x := Symbol_Table_Module_X.fetch_proc.
Definition fetch_type_x := Symbol_Table_Module_X.fetch_type.
Definition fetch_exp_type_x := Symbol_Table_Module_X.fetch_exp_type.
Definition update_vars_x := Symbol_Table_Module_X.update_vars.
Definition update_procs_x := Symbol_Table_Module_X.update_procs.
Definition update_types_x := Symbol_Table_Module_X.update_types.
Definition update_exps_x := Symbol_Table_Module_X.update_exps.

