Require Export language_flagged.


(* ***************************************************************
   generate and insert check flags into AST nodes according to the 
   run-time check rules;
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

Require Import X_SparkTactics.

(** * Lemmas *)
Lemma procedure_components_rel: forall p p',
  compile2_flagged_procedure_declaration p p' ->
  compile2_flagged_parameter_specifications (procedure_parameter_profile p) (procedure_parameter_profile_x p') /\
  compile2_flagged_declarations (procedure_declarative_part p) (procedure_declarative_part_x p') /\
  compile2_flagged_stmt (procedure_statements p) (procedure_statements_x p').
Proof.
  intros.
  inversion H; smack.
Qed.












