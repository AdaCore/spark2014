Require Export symboltable_module.
Require Export checks_generator.

(** * Symbol Tables *)

(* symbol table for unflagged program *)
Module Symbol_Table_Elements <: SymTable_Element.
  Definition Procedure_Decl := procedure_body.
  Definition Type_Decl := type_declaration.
End Symbol_Table_Elements.

Module Symbol_Table_Module := SymbolTableM (Symbol_Table_Elements).


(* symbol table for flagged program *)
Module Symbol_Table_Elements_X <: SymTable_Element.
  Definition Procedure_Decl := procedure_body_x.
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

Inductive compile2_flagged_proc_declaration_map: list (idnum * (level * procedure_body)) -> 
                                                 list (idnum * (level * procedure_body_x)) -> Prop :=
    | C2_Flagged_Proc_Declaration_Map_Null:
        compile2_flagged_proc_declaration_map nil nil
    | C2_Flagged_Proc_Declaration_Map: forall pd pd' pl pl' p l,
        compile2_flagged_procedure_body pd pd' ->
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

Lemma procedure_declaration_rel: forall ps ps' p n pb n' pb',
  compile2_flagged_proc_declaration_map ps ps' ->
    Symbol_Table_Module.SymTable_Procs.fetches p ps = Some (n, pb) ->
      Symbol_Table_Module_X.SymTable_Procs.fetches p ps' = Some (n', pb') ->
        n = n' /\ compile2_flagged_procedure_body pb pb'.
Proof.
  intros ps ps' p n pb n' pb' H; revert p n pb n' pb'.
  induction H; intros.
- inversion H; inversion H0; auto.
- unfold Symbol_Table_Module.SymTable_Procs.fetches in H1;
  unfold Symbol_Table_Module_X.SymTable_Procs.fetches in H2.
  remember (beq_nat p0 p) as Beq.
  destruct Beq. 
  + smack.
  + specialize (IHcompile2_flagged_proc_declaration_map _ _ _ _ _ H1 H2).
    auto.
Qed.

Lemma symbol_table_procedure_rel: forall p st n pb st' n' pb',
  Symbol_Table_Module.fetch_proc p st = Some (n, pb) ->
    Symbol_Table_Module_X.fetch_proc p st' = Some (n', pb') ->
      compile2_flagged_symbol_table st st' ->
        n = n' /\ compile2_flagged_procedure_body pb pb'.
Proof.
  intros.
  inversion H1; subst; clear H1.
  unfold Symbol_Table_Module_X.fetch_proc in H0;
  unfold Symbol_Table_Module.fetch_proc in H;
  simpl in H0, H.
  specialize (procedure_declaration_rel _ _ _ _ _ _ _ H2 H H0);
  auto.
Qed.

