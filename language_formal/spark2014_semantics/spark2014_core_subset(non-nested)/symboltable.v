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

Definition level := Symbol_Table_Module.level.

Inductive compile2_flagged_proc_declaration_map: list (idnum * (level * procedure_declaration)) -> 
                                                 list (idnum * (level * procedure_declaration_x)) -> Prop :=
    | C2_Flagged_Proc_Declaration_Map_Null:
        compile2_flagged_proc_declaration_map nil nil
    | C2_Flagged_Proc_Declaration_Map: forall pd pd' pl pl' p l,
        compile2_flagged_procedure_declaration pd pd' ->
        compile2_flagged_proc_declaration_map pl pl' ->
        compile2_flagged_proc_declaration_map ((p, (l, pd)) :: pl) ((p, (l, pd')) :: pl').

Inductive compile2_flagged_type_declaration_map: list (idnum * type_declaration) -> 
                                                 list (idnum * type_declaration_x) -> Prop :=
    | C2_Flagged_Type_Declaration_Map_Null:
        compile2_flagged_type_declaration_map nil nil
    | C2_Flagged_Type_Declaration_Map: forall t t' tl tl' x,
        compile2_flagged_type_declaration t t' ->
        compile2_flagged_type_declaration_map tl tl' ->
        compile2_flagged_type_declaration_map ((x, t) :: tl) ((x, t') :: tl').

Inductive compile2_flagged_symbol_table: symbol_table -> symbol_table' -> Prop := 
  | C2_Flagged_SymTable: forall p p' t t' x,
      compile2_flagged_proc_declaration_map p p' ->
      compile2_flagged_type_declaration_map t t' ->
      compile2_flagged_symbol_table (mkSymbolTable x p t) (mkSymbolTable' x p' t').


(** * Lemmas *)

Lemma symbol_table_procedure_rel: forall p st n pb st' n' pb',
  Symbol_Table_Module.fetch_proc p st = Some (n, pb) ->
    Symbol_Table_Module_X.fetch_proc p st' = Some (n', pb') ->
      compile2_flagged_symbol_table st st' ->
        n = n' /\ compile2_flagged_procedure_declaration pb pb'.
Proof.
  intros.
  admit.
Qed.

