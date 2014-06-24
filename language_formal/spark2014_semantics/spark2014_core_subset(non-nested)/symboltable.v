Require Export symboltable_module.
Require Export language_flagged.

(** * Symbol Tables *)

(* symbol table for unflagged program *)
Module Symbol_Table_Elements <: SymTable_Element.
  Definition Procedure_Decl := procedure_declaration.
  Definition Type_Decl := type_declaration.
End Symbol_Table_Elements.

Module Symbol_Table_Module := SymbolTableM (Symbol_Table_Elements).


(* symbol table for flagged program *)
Module Symbol_Table_Elements_X <: SymTable_Element.
  Definition Procedure_Decl := procedure_declaration_x.
  Definition Type_Decl := type_declaration_x.
End Symbol_Table_Elements_X.

Module Symbol_Table_Module_X := SymbolTableM (Symbol_Table_Elements_X).



(** * Compile To Flagged Symbol Table *)

Definition symbol_table := Symbol_Table_Module.symboltable.
Definition symbol_table' := Symbol_Table_Module_X.symboltable.

Definition mkSymbolTable := Symbol_Table_Module.mkSymbolTable.
Definition mkSymbolTable' := Symbol_Table_Module_X.mkSymbolTable.

Definition proc_decl := Symbol_Table_Module.proc_decl.
Definition type_decl := Symbol_Table_Module.type_decl.
Definition proc_decl' := Symbol_Table_Module_X.proc_decl.
Definition type_decl' := Symbol_Table_Module_X.type_decl.

(*
Inductive compile2_flagged_symbol_table: symbol_table -> symbol_table' -> Prop := 
  | C2_Flagged_SymTable_Null: forall x,
      compile2_flagged_symbol_table (mkSymbolTable x nil nil) (mkSymbolTable' x nil nil).
  | C2  
.
*)








