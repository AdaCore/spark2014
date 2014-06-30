Require Export language.
Require Export checks.


(* ****************************************************
   SPARK subset annotated with flagged run time checks
   **************************************************** *)

(** * SPARK Subset Language With Check Flags *)

(* Ada 2012 RM, Chapter 3. Declaration and Types *)

(** ** Expressions *)
(* Chapter 4 *)
(* now checks are only considered at the expression level *)
Inductive expression_x: Type := 
    | E_Literal_X: astnum -> literal -> check_flags -> expression_x (* 4.2 *)
    | E_Name_X: astnum -> name_x -> check_flags -> expression_x (* 4.1 *)
    | E_Binary_Operation_X: astnum -> binary_operator -> expression_x -> expression_x -> check_flags -> expression_x (* 4.5.3 and 4.5.5 *)
    | E_Unary_Operation_X: astnum -> unary_operator -> expression_x -> check_flags -> expression_x (* 4.5.4 *)  

with name_x: Type := (* 4.1 *)
    | E_Identifier_X: astnum -> idnum -> check_flags -> name_x (* 4.1 *)
    | E_Indexed_Component_X: astnum -> astnum -> idnum -> expression_x -> check_flags -> name_x (* 4.1.1 *)
    | E_Selected_Component_X: astnum -> astnum -> idnum -> idnum -> check_flags -> name_x (* 4.1.3 *). (* the first astnum for the record field and second one for record *)

(** ** Statements *)
(* Chapter 5 *)
(* Sequence is not a statement in Ada, it's a shortcut for now;
   check flags can be easily added if they are needed later;
*)
Inductive statement_x: Type := 
    | S_Null_X: statement_x (* 5.1 *)
    | S_Assignment_X: astnum -> name_x -> expression_x -> statement_x (* 5.2 *)
    | S_If_X: astnum -> expression_x -> statement_x -> statement_x -> statement_x (* 5.3 *)
    | S_While_Loop_X: astnum -> expression_x -> statement_x -> statement_x (* 5.5 *)
    | S_Procedure_Call_X: astnum -> astnum -> procnum -> list expression_x -> statement_x (* 6.4 *) (* the second astnum for the called procedure *)
    | S_Sequence_X: astnum -> statement_x -> statement_x -> statement_x. (* 5.1 *)


Inductive type_declaration_x: Type := (* 3.2.1 *)
    | Array_Type_Declaration_X: (* Constrained_Array_Definition, non-nested one-dimentional array *)
        astnum -> typenum (*array name*) -> type (*component type*) -> 
          Z (*lower bound*) -> Z (*upper bound*) -> type_declaration_x (* 3.6 *)
    | Record_Type_Declaration_X: 
        astnum -> typenum (*record name*) -> list (idnum * type (*field type*)) -> type_declaration_x (* 3.8 *).

(* 3.3.1 *)
Record object_declaration_x: Type := mkobject_declaration_x{
    declaration_astnum_x: astnum;
    object_name_x: idnum;
    object_nominal_subtype_x: type;
    initialization_expression_x: option (expression_x)
}.

(* 6.1 (15/3) *)
Record parameter_specification_x: Type := mkparameter_specification_x{
    parameter_astnum_x: astnum;
    parameter_name_x: idnum;
    parameter_subtype_mark_x: type;
    parameter_mode_x: mode
(*  parameter_default_expression_x: option (expression_x) *)
}.

(* 13.1.1 *)
Record aspect_specification_x: Type := mkaspect_specification_x{
    aspect_astnum_x: astnum;
    aspect_mark_x: aspectnum;
    aspect_definition_x: expression_x
}.

(* Mutual records/inductives are not allowed in coq, so we build a record by hand. *)
Inductive declaration_x: Type :=  (* 3.1 *)
    | D_Object_Declaration_X: astnum -> object_declaration_x -> declaration_x (* 3.3.1 *) 
    | D_Procedure_Declaration_X: astnum -> procedure_declaration_x -> declaration_x (* 6.1 *)
    | D_Type_Declaration_X: astnum -> type_declaration_x -> declaration_x (* 3.2.1 *)
 (* | package_declaration 
    | Other_Declarations *)

with procedure_declaration_x: Type :=
  mkprocedure_declaration_x
    (procedure_astnum_x: astnum)
    (procedure_name_x: procnum)
    (procedure_contracts_x: list aspect_specification_x)
    (procedure_parameter_profile_x: list parameter_specification_x)
    (procedure_declarative_part_x: list declaration_x)
    (procedure_statements_x: statement_x).


(** ** Compilation Unit Subprogram *)
(* 6.1 *)
Inductive subprogram_x: Type := 
    | Global_Procedure_X: astnum -> procedure_declaration_x -> subprogram_x
(*  | Global_Function_X: astnum -> function_declaration_x -> subprogram_x *).

(* 10.1.1 *)
Inductive library_unit_declaration_x: Type := 
    | Library_Subprogram_X: astnum -> subprogram_x -> library_unit_declaration_x.

(* 10.1.1 *)
Inductive compilation_unit_x: Type := 
    | Library_Unit_X: astnum -> library_unit_declaration_x -> compilation_unit_x.



Section AuxiliaryFunctions_X.

  Definition procedure_statements_x pb :=
    match pb with 
      | mkprocedure_declaration_x _ _ _ _ _ x => x
    end.

  Definition procedure_declarative_part_x pb :=
    match pb with
      | mkprocedure_declaration_x _ _ _ _ x _ => x
    end.

  Definition procedure_parameter_profile_x pb :=
    match pb with
      | mkprocedure_declaration_x _ _ _ x _ _ => x
    end.

  Definition procedure_name_x pb :=
    match pb with
      | mkprocedure_declaration_x _ x _ _ _ _ => x
    end.

  Definition type_name_x td :=
    match td with
    | Array_Type_Declaration_X _ tn _ _ _ => tn
    | Record_Type_Declaration_X _ tn _ => tn
    end.

End AuxiliaryFunctions_X.



(* ***************************************************************
   generate and insert check flags into AST nodes according to the 
   check flag generator;
   *************************************************************** *)

(** * Compile To Flagged Program *)

Inductive compile2_flagged_exp: expression -> expression_x -> Prop :=
    | C2_Flagged_Literal: forall ast_num l checkflags,
        gen_check_flags (E_Literal ast_num l) checkflags ->
        compile2_flagged_exp (E_Literal ast_num l) (E_Literal_X ast_num l checkflags) 
    | C2_Flagged_Name: forall ast_num n checkflags n_flagged,
        gen_check_flags (E_Name ast_num n) checkflags ->
        compile2_flagged_name n n_flagged ->
        compile2_flagged_exp (E_Name ast_num n) (E_Name_X ast_num n_flagged checkflags) 
    | C2_Flagged_Binary_Operation: forall ast_num op e1 e2 checkflags e1_flagged e2_flagged,
        gen_check_flags (E_Binary_Operation ast_num op e1 e2) checkflags ->
        compile2_flagged_exp e1 e1_flagged ->
        compile2_flagged_exp e2 e2_flagged ->
        compile2_flagged_exp (E_Binary_Operation ast_num op e1 e2)
                             (E_Binary_Operation_X ast_num op e1_flagged e2_flagged checkflags)
    | C2_Flagged_Unary_Operation: forall ast_num op e checkflags e_flagged,
        gen_check_flags (E_Unary_Operation ast_num op e) checkflags ->
        compile2_flagged_exp e e_flagged ->
        compile2_flagged_exp (E_Unary_Operation ast_num op e) 
                             (E_Unary_Operation_X ast_num op e_flagged checkflags)
        
with compile2_flagged_name: name -> name_x -> Prop :=
    | C2_Flagged_Identifier: forall ast_num x checkflags,
        gen_name_check_flags (E_Identifier ast_num x) checkflags ->
        compile2_flagged_name (E_Identifier ast_num x) (E_Identifier_X ast_num x checkflags) 
    | C2_Flagged_Indexed_Component: forall ast_num x_ast_num x e checkflags e_flagged,
        gen_name_check_flags (E_Indexed_Component ast_num x_ast_num x e) checkflags ->
        compile2_flagged_exp e e_flagged ->
        compile2_flagged_name (E_Indexed_Component ast_num x_ast_num x e) 
                              (E_Indexed_Component_X ast_num x_ast_num x e_flagged checkflags) 
    | C2_Flagged_Selected_Component: forall ast_num x_ast_num x f checkflags,
        gen_name_check_flags (E_Selected_Component ast_num x_ast_num x f) checkflags ->
        compile2_flagged_name (E_Selected_Component ast_num x_ast_num x f) 
                              (E_Selected_Component_X ast_num x_ast_num x f checkflags).

Inductive compile2_flagged_exps: list expression -> list expression_x -> Prop :=
    | C2_Flagged_Exps_Null:
        compile2_flagged_exps nil nil 
    | C2_Flagged_Exps_List: forall e e_flagged le le_flagged,
        compile2_flagged_exp  e  e_flagged ->
        compile2_flagged_exps le le_flagged ->
        compile2_flagged_exps (e :: le) (e_flagged :: le_flagged).


Inductive compile2_flagged_stmt: statement -> statement_x -> Prop := 
    | C2_Flagged_Null:
        compile2_flagged_stmt S_Null S_Null_X 
    | C2_Flagged_Assignment: forall x x_flagged e e_flagged ast_num,
        compile2_flagged_name x x_flagged ->
        compile2_flagged_exp  e e_flagged -> 
        compile2_flagged_stmt (S_Assignment   ast_num x e) 
                              (S_Assignment_X ast_num x_flagged e_flagged) 
    | C2_Flagged_If: forall e e_flagged c1 c1_flagged c2 c2_flagged ast_num,
        compile2_flagged_exp  e  e_flagged ->
        compile2_flagged_stmt c1 c1_flagged ->
        compile2_flagged_stmt c2 c2_flagged ->
        compile2_flagged_stmt (S_If   ast_num e c1 c2) 
                              (S_If_X ast_num e_flagged c1_flagged c2_flagged)
    | C2_Flagged_While: forall e e_flagged c c_flagged ast_num,
        compile2_flagged_exp  e e_flagged ->
        compile2_flagged_stmt c c_flagged ->
        compile2_flagged_stmt (S_While_Loop   ast_num e c) 
                              (S_While_Loop_X ast_num e_flagged c_flagged)
    | C2_Flagged_Procedure_Call: forall args args_flagged ast_num p_ast_num p,
        compile2_flagged_exps args args_flagged ->
        compile2_flagged_stmt (S_Procedure_Call   ast_num p_ast_num p args) 
                              (S_Procedure_Call_X ast_num p_ast_num p args_flagged)
    | C2_Flagged_Sequence: forall c1 c1_flagged c2 c2_flagged ast_num,
        compile2_flagged_stmt c1 c1_flagged ->
        compile2_flagged_stmt c2 c2_flagged ->
        compile2_flagged_stmt (S_Sequence ast_num   c1 c2)
                              (S_Sequence_X ast_num c1_flagged c2_flagged).


Inductive compile2_flagged_type_declaration: type_declaration -> type_declaration_x -> Prop :=
    | C2_Flagged_Array_Type_Decl: forall ast_num tn t l u,
        compile2_flagged_type_declaration (Array_Type_Declaration   ast_num tn t l u)
                                          (Array_Type_Declaration_X ast_num tn t l u)
    | C2_Flagged_Record_Type_Decl: forall ast_num tn fs,
        compile2_flagged_type_declaration (Record_Type_Declaration   ast_num tn fs) 
                                          (Record_Type_Declaration_X ast_num tn fs).


Inductive compile2_flagged_object_declaration: object_declaration -> object_declaration_x -> Prop :=
    | C2_Flagged_Object_Declaration_NoneInit: forall ast_num x t,
        compile2_flagged_object_declaration (mkobject_declaration   ast_num x t None) 
                                            (mkobject_declaration_x ast_num x t None) 
    | C2_Flagged_Object_Declaration: forall e e_flagged ast_num x t,
        compile2_flagged_exp e e_flagged ->
        compile2_flagged_object_declaration (mkobject_declaration   ast_num x t (Some e)) 
                                            (mkobject_declaration_x ast_num x t (Some e_flagged)).

Inductive compile2_flagged_object_declarations: list object_declaration -> list object_declaration_x -> Prop :=
    | C2_Flagged_Object_Declarations_Null:
        compile2_flagged_object_declarations nil nil 
    | C2_Flagged_Object_Declarations_List: forall o o_flagged lo lo_flagged,
        compile2_flagged_object_declaration  o o_flagged ->
        compile2_flagged_object_declarations lo lo_flagged ->
        compile2_flagged_object_declarations (o :: lo) (o_flagged :: lo_flagged).


Inductive compile2_flagged_parameter_specification: parameter_specification -> parameter_specification_x -> Prop :=
    | C2_Flagged_Parameter_Spec: forall ast_num x t m,
        compile2_flagged_parameter_specification (mkparameter_specification   ast_num x t m)
                                                 (mkparameter_specification_x ast_num x t m).

Inductive compile2_flagged_parameter_specifications: list parameter_specification -> list parameter_specification_x -> Prop :=
    | C2_Flagged_Parameter_Specs_Null:
        compile2_flagged_parameter_specifications nil nil
    | C2_Flagged_Parameter_Specs_List: forall param param_flagged lparam lparam_flagged,
        compile2_flagged_parameter_specification  param  param_flagged ->
        compile2_flagged_parameter_specifications lparam lparam_flagged ->
        compile2_flagged_parameter_specifications (param :: lparam) (param_flagged :: lparam_flagged).


Inductive compile2_flagged_aspect_specification: aspect_specification -> aspect_specification_x -> Prop :=
    | C2_Flagged_Aspect_Spec: forall e e_flagged ast_num mk,
        compile2_flagged_exp e e_flagged ->
        compile2_flagged_aspect_specification (mkaspect_specification   ast_num mk e) 
                                              (mkaspect_specification_x ast_num mk e_flagged).

Inductive compile2_flagged_aspect_specifications: list aspect_specification -> list aspect_specification_x -> Prop :=
    | C2_Flagged_Aspect_Specs_Null: 
        compile2_flagged_aspect_specifications nil nil 
    | C2_Flagged_Aspect_Specs_List: forall aspect aspect_flagged laspect laspect_flagged,
        compile2_flagged_aspect_specification  aspect  aspect_flagged ->
        compile2_flagged_aspect_specifications laspect laspect_flagged ->
        compile2_flagged_aspect_specifications (aspect :: laspect) (aspect_flagged :: laspect_flagged).


Inductive compile2_flagged_declaration: declaration -> declaration_x -> Prop :=
    | C2_Flagged_D_Object_Declaration: forall o o_flagged ast_num,
        compile2_flagged_object_declaration o o_flagged ->
        compile2_flagged_declaration (D_Object_Declaration   ast_num o)
                                     (D_Object_Declaration_X ast_num o_flagged) 
    | C2_Flagged_D_Procedure_Declaration: forall p p_flagged ast_num,
        compile2_flagged_procedure_declaration p p_flagged ->
        compile2_flagged_declaration (D_Procedure_Declaration   ast_num p)
                                     (D_Procedure_Declaration_X ast_num p_flagged) 
    | C2_Flagged_D_Type_Declaration: forall t t_flagged ast_num,
        compile2_flagged_type_declaration t t_flagged ->
        compile2_flagged_declaration (D_Type_Declaration   ast_num t) 
                                     (D_Type_Declaration_X ast_num t_flagged)

with compile2_flagged_procedure_declaration: procedure_declaration -> procedure_declaration_x -> Prop :=
       | C2_Flagged_Procedure_Declaration: forall aspects aspects_flagged params params_flagged 
                                                  decls decls_flagged stmt stmt_flagged ast_num p,
           compile2_flagged_aspect_specifications aspects aspects_flagged ->
           compile2_flagged_parameter_specifications params params_flagged ->
           compile2_flagged_declarations decls decls_flagged ->
           compile2_flagged_stmt stmt stmt_flagged ->
           compile2_flagged_procedure_declaration (mkprocedure_declaration   ast_num p aspects params decls stmt)
                                                  (mkprocedure_declaration_x ast_num p aspects_flagged params_flagged decls_flagged stmt_flagged)

with compile2_flagged_declarations: list declaration -> list declaration_x -> Prop :=
       | C2_Flagged_Declarations_Null:
           compile2_flagged_declarations nil nil 
       | C2_Flagged_Declarations_List: forall d d_flagged ld ld_flagged,
           compile2_flagged_declaration  d  d_flagged ->
           compile2_flagged_declarations ld ld_flagged ->
           compile2_flagged_declarations (d :: ld) (d_flagged :: ld_flagged).


(*
Inductive compile2_flagged_subprogram: subprogram -> subprogram_x -> Prop :=
    | C2_Flagged_Subprogram: p p_flagged ast_num
        compile2_flagged_procedure_declaration p p_flagged ->
        compile2_flagged_subprogram (Global_Procedure ast_num p) 
                                    (Global_Procedure_X ast_num p_flagged).
*)


(** * Lemmas *)
Lemma procedure_components_rel: forall p p',
  compile2_flagged_procedure_declaration p p' ->
  compile2_flagged_parameter_specifications (procedure_parameter_profile p) (procedure_parameter_profile_x p') /\
  compile2_flagged_declarations (procedure_declarative_part p) (procedure_declarative_part_x p') /\
  compile2_flagged_stmt (procedure_statements p) (procedure_statements_x p').
Proof.
  intros.
  admit.
Qed.












