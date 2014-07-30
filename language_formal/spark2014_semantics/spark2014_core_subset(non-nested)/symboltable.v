Require Export symboltable_module.
Require Export language_flagged.

(** * Symbol Tables *)

(** it's used to map back to the source location once an error is detected in ast tree *)
Record source_location := sloc{
  line   : nat; 
  col    : nat; 
  endline: nat; 
  endcol : nat
}.

(* symbol table for unflagged program *)
Module Symbol_Table_Elements <: SymTable_Element.
  Definition Procedure_Decl := procedure_body.
  Definition Type_Decl := type_declaration.
  Definition Source_Location := source_location.
End Symbol_Table_Elements.

(* symbol table for flagged program *)
Module Symbol_Table_Elements_X <: SymTable_Element.
  Definition Procedure_Decl := procedure_body_x.
  Definition Type_Decl := type_declaration_x.
  Definition Source_Location := source_location.
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
Definition reside_symtable_sloc := Symbol_Table_Module.reside_symtable_sloc.
Definition fetch_var := Symbol_Table_Module.fetch_var.
Definition fetch_proc := Symbol_Table_Module.fetch_proc.
Definition fetch_type := Symbol_Table_Module.fetch_type.
Definition fetch_exp_type := Symbol_Table_Module.fetch_exp_type.
Definition fetch_sloc := Symbol_Table_Module.fetch_sloc.
Definition update_vars := Symbol_Table_Module.update_vars.
Definition update_procs := Symbol_Table_Module.update_procs.
Definition update_types := Symbol_Table_Module.update_types.
Definition update_exps := Symbol_Table_Module.update_exps.
Definition update_sloc := Symbol_Table_Module.update_sloc.

Definition reside_symtable_vars_x := Symbol_Table_Module_X.reside_symtable_vars.
Definition reside_symtable_procs_x := Symbol_Table_Module_X.reside_symtable_procs.
Definition reside_symtable_types_x := Symbol_Table_Module_X.reside_symtable_types.
Definition reside_symtable_exps_x := Symbol_Table_Module_X.reside_symtable_exps.
Definition reside_symtable_sloc_x := Symbol_Table_Module_X.reside_symtable_sloc.
Definition fetch_var_x := Symbol_Table_Module_X.fetch_var.
Definition fetch_proc_x := Symbol_Table_Module_X.fetch_proc.
Definition fetch_type_x := Symbol_Table_Module_X.fetch_type.
Definition fetch_exp_type_x := Symbol_Table_Module_X.fetch_exp_type.
Definition fetch_sloc_x := Symbol_Table_Module_X.fetch_sloc.
Definition update_vars_x := Symbol_Table_Module_X.update_vars.
Definition update_procs_x := Symbol_Table_Module_X.update_procs.
Definition update_types_x := Symbol_Table_Module_X.update_types.
Definition update_exps_x := Symbol_Table_Module_X.update_exps.
Definition update_sloc_x := Symbol_Table_Module_X.update_sloc.

Inductive extract_subtype_range: symboltable -> type -> range -> Prop :=
  | Extract_Range: forall t tn st td l u,
      subtype_num t = Some tn ->
      fetch_type tn st = Some td ->
      subtype_range td = Some (Range l u) ->
      extract_subtype_range st t (Range l u).

(* tm is a subtype_mark *)
Inductive extract_array_index_range: symboltable -> typenum -> range -> Prop :=
  | Extract_Index_Range: forall t st a_ast_num tn tm typ tn' td l u, 
      fetch_type t st = Some (Array_Type_Declaration a_ast_num tn tm typ) ->
      subtype_num tm = Some tn' ->
      fetch_type tn' st = Some td ->
      subtype_range td = Some (Range l u) ->
      extract_array_index_range st t (Range l u).

Inductive extract_subtype_range_x: symboltable_x -> type -> range_x -> Prop :=
  | Extract_Range_X: forall t tn st td l u,
      subtype_num t = Some tn ->
      fetch_type_x tn st = Some td ->
      subtype_range_x td = Some (Range_X l u) ->
      extract_subtype_range_x st t (Range_X l u).

(* tm is a subtype_mark *)
Inductive extract_array_index_range_x: symboltable_x -> typenum -> range_x -> Prop :=
  | Extract_Index_Range_X: forall t st a_ast_num tn tm typ tn' td l u, 
      fetch_type_x t st = Some (Array_Type_Declaration_X a_ast_num tn tm typ) ->
      subtype_num tm = Some tn' ->
      fetch_type_x tn' st = Some td ->
      subtype_range_x td = Some (Range_X l u) ->
      extract_array_index_range_x st t (Range_X l u).
