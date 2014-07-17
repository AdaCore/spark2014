Require Export language_flagged.


(* ***************************************************************
   generate and insert check flags into AST nodes according to the 
   run-time check rules;
   *************************************************************** *)

(** * Compile To Flagged Program *)

Inductive compile2_flagged_exp: expression -> expression_x -> Prop :=
    | C2_Flagged_Literal: forall ast_num l checkflags,
        gen_exp_check_flags (E_Literal ast_num l) checkflags ->
        compile2_flagged_exp (E_Literal ast_num l) (E_Literal_X ast_num l checkflags) 
    | C2_Flagged_Name: forall ast_num n checkflags n_flagged,
        gen_exp_check_flags (E_Name ast_num n) checkflags ->
        compile2_flagged_name n n_flagged ->
        compile2_flagged_exp (E_Name ast_num n) (E_Name_X ast_num n_flagged checkflags) 
    | C2_Flagged_Binary_Operation: forall ast_num op e1 e2 checkflags e1_flagged e2_flagged,
        gen_exp_check_flags (E_Binary_Operation ast_num op e1 e2) checkflags ->
        compile2_flagged_exp e1 e1_flagged ->
        compile2_flagged_exp e2 e2_flagged ->
        compile2_flagged_exp (E_Binary_Operation ast_num op e1 e2)
                             (E_Binary_Operation_X ast_num op e1_flagged e2_flagged checkflags)
    | C2_Flagged_Unary_Operation: forall ast_num op e checkflags e_flagged,
        gen_exp_check_flags (E_Unary_Operation ast_num op e) checkflags ->
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
    | C2_Flagged_D_Null_Declaration: 
        compile2_flagged_declaration D_Null_Declaration D_Null_Declaration_X
    | C2_Flagged_D_Type_Declaration: forall t t_flagged ast_num,
        compile2_flagged_type_declaration t t_flagged ->
        compile2_flagged_declaration (D_Type_Declaration   ast_num t) 
                                     (D_Type_Declaration_X ast_num t_flagged)
    | C2_Flagged_D_Object_Declaration: forall o o_flagged ast_num,
        compile2_flagged_object_declaration o o_flagged ->
        compile2_flagged_declaration (D_Object_Declaration   ast_num o)
                                     (D_Object_Declaration_X ast_num o_flagged) 
    | C2_Flagged_D_Procedure_Declaration: forall p p_flagged ast_num,
        compile2_flagged_procedure_body p p_flagged ->
        compile2_flagged_declaration (D_Procedure_Body   ast_num p)
                                     (D_Procedure_Body_X ast_num p_flagged) 
    | C2_Flagged_D_Seq_Declaration: forall d1 d1_flagged d2 d2_flagged ast_num,
        compile2_flagged_declaration d1 d1_flagged ->
        compile2_flagged_declaration d2 d2_flagged ->
        compile2_flagged_declaration (D_Seq_Declaration ast_num d1 d2) (D_Seq_Declaration_X ast_num d1_flagged d2_flagged)

with compile2_flagged_procedure_body: procedure_body -> procedure_body_x -> Prop :=
       | C2_Flagged_Procedure_Declaration: forall aspects aspects_flagged params params_flagged 
                                                  decls decls_flagged stmt stmt_flagged ast_num p,
           compile2_flagged_aspect_specifications aspects aspects_flagged ->
           compile2_flagged_parameter_specifications params params_flagged ->
           compile2_flagged_declaration decls decls_flagged ->
           compile2_flagged_stmt stmt stmt_flagged ->
           compile2_flagged_procedure_body (mkprocedure_body   ast_num p params aspects decls stmt)
                                                  (mkprocedure_body_x ast_num p params_flagged aspects_flagged decls_flagged stmt_flagged).


(* ***************************************************************
                          Funtion Version
   *************************************************************** *)

(** * Translator Function To Insert Checks *)

Function compile2_flagged_exp_f (e: expression): expression_x :=
  match e with
  | E_Literal ast_num l => 
      let checkflags := gen_exp_check_flags_f (E_Literal ast_num l) in
        (E_Literal_X ast_num l checkflags)
  | E_Name ast_num n => 
      let checkflags := gen_exp_check_flags_f (E_Name ast_num n) in
      let n_flagged := compile2_flagged_name_f n in
        (E_Name_X ast_num n_flagged checkflags)
  | E_Binary_Operation ast_num op e1 e2 =>
      let checkflags := gen_exp_check_flags_f (E_Binary_Operation ast_num op e1 e2) in
      let e1_flagged := compile2_flagged_exp_f e1 in
      let e2_flagged := compile2_flagged_exp_f e2 in
        (E_Binary_Operation_X ast_num op e1_flagged e2_flagged checkflags)
  | E_Unary_Operation ast_num op e => 
      let checkflags := gen_exp_check_flags_f (E_Unary_Operation ast_num op e) in
      let e_flagged := compile2_flagged_exp_f e in
        (E_Unary_Operation_X ast_num op e_flagged checkflags)
  end

with compile2_flagged_name_f (n: name): name_x :=
  match n with
  | E_Identifier ast_num x =>
      let checkflags := gen_name_check_flags_f (E_Identifier ast_num x) in
        (E_Identifier_X ast_num x checkflags)
  | E_Indexed_Component ast_num x_ast_num x e =>
      let checkflags := gen_name_check_flags_f (E_Indexed_Component ast_num x_ast_num x e) in
      let e_flagged := compile2_flagged_exp_f e in
        (E_Indexed_Component_X ast_num x_ast_num x e_flagged checkflags)
  | E_Selected_Component ast_num x_ast_num x f =>
      let checkflags := gen_name_check_flags_f (E_Selected_Component ast_num x_ast_num x f) in
        (E_Selected_Component_X ast_num x_ast_num x f checkflags)
  end.

Function compile2_flagged_exps_f (le: list expression): list expression_x :=
  match le with
  | nil => nil
  | e :: le' => 
      let e_flagged := compile2_flagged_exp_f e in
      let le_flagged := compile2_flagged_exps_f le' in
        (e_flagged :: le_flagged)
  end.

Function compile2_flagged_stmt_f (c: statement): statement_x :=
  match c with
  | S_Null => S_Null_X
  | S_Assignment ast_num x e =>
      let x_flagged := compile2_flagged_name_f x in
      let e_flagged := compile2_flagged_exp_f  e in
        (S_Assignment_X ast_num x_flagged e_flagged)
  | S_If ast_num e c1 c2 =>
      let e_flagged := compile2_flagged_exp_f e in
      let c1_flagged := compile2_flagged_stmt_f c1 in
      let c2_flagged := compile2_flagged_stmt_f c2 in
        (S_If_X ast_num e_flagged c1_flagged c2_flagged)
  | S_While_Loop ast_num e c =>
      let e_flagged := compile2_flagged_exp_f e in
      let c_flagged := compile2_flagged_stmt_f c in
        (S_While_Loop_X ast_num e_flagged c_flagged)
  | S_Procedure_Call ast_num p_ast_num p args =>
      let args_flagged := compile2_flagged_exps_f args in
        (S_Procedure_Call_X ast_num p_ast_num p args_flagged)
  | S_Sequence ast_num c1 c2 =>
      let c1_flagged := compile2_flagged_stmt_f c1 in
      let c2_flagged := compile2_flagged_stmt_f c2 in
        (S_Sequence_X ast_num c1_flagged c2_flagged)
  end.

Function compile2_flagged_type_declaration_f (t: type_declaration): type_declaration_x :=
  match t with
  | Array_Type_Declaration ast_num tn t l u => 
      (Array_Type_Declaration_X ast_num tn t l u)
  | Record_Type_Declaration ast_num tn fs =>
      (Record_Type_Declaration_X ast_num tn fs)
  end.

Function compile2_flagged_object_declaration_f (o: object_declaration): object_declaration_x :=
  match o with
  | mkobject_declaration ast_num x t None =>
      (mkobject_declaration_x ast_num x t None)
  | mkobject_declaration ast_num x t (Some e) => 
      let e_flagged := compile2_flagged_exp_f e in
        (mkobject_declaration_x ast_num x t (Some e_flagged))
  end.

Function compile2_flagged_object_declarations_f (lo: list object_declaration): list object_declaration_x :=
  match lo with
  | nil => nil
  | o :: lo' => 
      let o_flagged := compile2_flagged_object_declaration_f o in
      let lo_flagged := compile2_flagged_object_declarations_f lo' in
        (o_flagged :: lo_flagged)
  end.

Function compile2_flagged_parameter_specification_f (param: parameter_specification): parameter_specification_x :=
  match param with
  | mkparameter_specification   ast_num x t m =>
      (mkparameter_specification_x ast_num x t m)
  end.

Function compile2_flagged_parameter_specifications_f (lparam: list parameter_specification): list parameter_specification_x :=
  match lparam with
  | nil => nil
  | param :: lparam' =>
      let param_flagged := compile2_flagged_parameter_specification_f param in
      let lparam_flagged := compile2_flagged_parameter_specifications_f lparam' in
        (param_flagged :: lparam_flagged)
  end.

Function compile2_flagged_aspect_specification_f (a: aspect_specification): aspect_specification_x :=
  match a with
  | mkaspect_specification ast_num mk e =>
      let e_flagged := compile2_flagged_exp_f e in
        (mkaspect_specification_x ast_num mk e_flagged)
  end.

Function compile2_flagged_aspect_specifications_f (la: list aspect_specification): list aspect_specification_x :=
  match la with
  | nil => nil
  | a :: la' =>
      let a_flagged := compile2_flagged_aspect_specification_f a in
      let la_flagged := compile2_flagged_aspect_specifications_f la' in
        (a_flagged :: la_flagged)
  end.


Function compile2_flagged_declaration_f (d: declaration): declaration_x :=
  match d with
  | D_Null_Declaration => D_Null_Declaration_X
  | D_Type_Declaration ast_num t =>
      let t_flagged := compile2_flagged_type_declaration_f t in
        (D_Type_Declaration_X ast_num t_flagged)
  | D_Object_Declaration ast_num o =>
      let o_flagged := compile2_flagged_object_declaration_f o in
        (D_Object_Declaration_X ast_num o_flagged)
  | D_Procedure_Body ast_num p =>
      let p_flagged := compile2_flagged_procedure_body_f p in
        (D_Procedure_Body_X ast_num p_flagged)
  | D_Seq_Declaration ast_num d1 d2 =>
      let d1_flagged := compile2_flagged_declaration_f d1 in
      let d2_flagged := compile2_flagged_declaration_f d2 in
        (D_Seq_Declaration_X ast_num d1_flagged d2_flagged)
  end

with compile2_flagged_procedure_body_f (p: procedure_body): procedure_body_x :=
  match p with
  | mkprocedure_body ast_num p params aspects decls stmt =>
      let aspects_flagged := compile2_flagged_aspect_specifications_f aspects in
      let params_flagged := compile2_flagged_parameter_specifications_f params in
      let decls_flagged := compile2_flagged_declaration_f decls in
      let stmt_flagged := compile2_flagged_stmt_f stmt in
        (mkprocedure_body_x ast_num p params_flagged aspects_flagged decls_flagged stmt_flagged)
  end.

(*
Function compile2_flagged_declaration_f11 (d: declaration): declaration_x :=
  match d with
  | D_Null_Declaration => D_Null_Declaration_X
  | D_Object_Declaration ast_num o =>
      let o_flagged := compile2_flagged_object_declaration_f o in
        (D_Object_Declaration_X ast_num o_flagged)
  | D_Type_Declaration ast_num t =>
      let t_flagged := compile2_flagged_type_declaration_f t in
        (D_Type_Declaration_X ast_num t_flagged)
  | D_Procedure_Body ast_num p =>
      let p_flagged :=
          match p with
          | mkprocedure_body ast_num p params aspects decls stmt =>
              let aspects_flagged := compile2_flagged_aspect_specifications_f aspects in
              let params_flagged := compile2_flagged_parameter_specifications_f params in
              let decls_flagged := compile2_flagged_declaration_f decls in
              let stmt_flagged := compile2_flagged_stmt_f stmt in
                (mkprocedure_body_x ast_num p params_flagged aspects_flagged decls_flagged stmt_flagged)
          end in
        (D_Procedure_Body_X ast_num p_flagged)
  | D_Seq_Declaration ast_num d1 d2 =>
      let d1_flagged := compile2_flagged_declaration_f d1 in
      let d2_flagged := compile2_flagged_declaration_f d2 in
        (D_Seq_Declaration_X ast_num d1_flagged d2_flagged)
  end.
*)


(* ***************************************************************
                 Semantics Equivalence Proof
   *************************************************************** *)

(** * Semantics Equivalence Proof For Translator *)

Scheme expression_ind := Induction for expression Sort Prop 
                         with name_ind := Induction for name Sort Prop.

Lemma compile2_flagged_exp_f_correctness: forall e e',
  compile2_flagged_exp_f e = e' ->
    compile2_flagged_exp e e'.
Proof.
  apply (expression_ind
    (fun e: expression => forall (e' : expression_x),
      compile2_flagged_exp_f e = e' ->
      compile2_flagged_exp e e')
    (fun n: name => forall (n': name_x),
      compile2_flagged_name_f n = n' ->
      compile2_flagged_name n n')
    ); smack;
  [destruct l | | destruct b | destruct u | | | ];
  repeat progress constructor; smack.
Qed.

Lemma compile2_flagged_name_f_correctness: forall e e',
  compile2_flagged_name_f e = e' ->
    compile2_flagged_name e e'.
Proof.
  intros.
  destruct e; smack;
  repeat progress constructor;
  apply compile2_flagged_exp_f_correctness; auto.  
Qed.

Lemma compile2_flagged_exps_f_correctness: forall le le',
  compile2_flagged_exps_f le = le' ->
    compile2_flagged_exps le le'.
Proof.
  induction le; smack.
- constructor.
- constructor.
  + apply compile2_flagged_exp_f_correctness; auto.
  + auto.
Qed.
  
Lemma compile2_flagged_stmt_f_correctness: forall c c',
  compile2_flagged_stmt_f c = c' ->
    compile2_flagged_stmt c c'.
Proof.
  induction c; smack.
- constructor.
- constructor;
  [ apply compile2_flagged_name_f_correctness |
    apply compile2_flagged_exp_f_correctness 
  ]; auto.
- constructor;
  [ apply compile2_flagged_exp_f_correctness | | ];
  smack.
- constructor;
  [ apply compile2_flagged_exp_f_correctness | ];
  smack.
- constructor;
  apply compile2_flagged_exps_f_correctness; auto.
- constructor; auto.
Qed.

Lemma compile2_flagged_type_declaration_f_correctness: forall t t',
  compile2_flagged_type_declaration_f t = t' ->
      compile2_flagged_type_declaration t t'.
Proof.
  destruct t; smack;
  constructor.  
Qed.

Lemma compile2_flagged_object_declaration_f_correctness: forall o o',
  compile2_flagged_object_declaration_f o = o' ->
    compile2_flagged_object_declaration o o'.
Proof.
  intros. 
  functional induction compile2_flagged_object_declaration_f o; smack;
  constructor.
  apply compile2_flagged_exp_f_correctness; auto.
Qed.

Lemma compile2_flagged_object_declarations_f_correctness: forall lo lo',
  compile2_flagged_object_declarations_f lo = lo' ->
    compile2_flagged_object_declarations lo lo'.
Proof.
  induction lo; smack; 
  constructor; smack.
  apply compile2_flagged_object_declaration_f_correctness; auto.   
Qed.

Lemma compile2_flagged_parameter_specification_f_correctness: forall param param',
  compile2_flagged_parameter_specification_f param = param' ->
    compile2_flagged_parameter_specification param param'.
Proof.
  smack;
  destruct param;
  constructor.  
Qed.

Lemma compile2_flagged_parameter_specifications_f_correctness: forall lparam lparam',
  compile2_flagged_parameter_specifications_f lparam = lparam' ->
    compile2_flagged_parameter_specifications lparam lparam'.
Proof.
  induction lparam; smack;
  constructor; smack.
  apply compile2_flagged_parameter_specification_f_correctness; auto.
Qed.

Lemma compile2_flagged_aspect_specification_f_correctness: forall a a',
  compile2_flagged_aspect_specification_f a = a' ->
    compile2_flagged_aspect_specification a a'.
Proof.
  smack;
  destruct a; constructor.
  apply compile2_flagged_exp_f_correctness; auto.
Qed.

Lemma compile2_flagged_aspect_specifications_f_correctness: forall la la',
  compile2_flagged_aspect_specifications_f la = la' ->
    compile2_flagged_aspect_specifications la la'.
Proof.
  induction la; smack;
  constructor; smack.
  apply compile2_flagged_aspect_specification_f_correctness; auto.
Qed.


Scheme declaration_ind := Induction for declaration Sort Prop 
                          with procedure_body_ind := Induction for procedure_body Sort Prop.

Lemma compile2_flagged_declaration_f_correctness: forall d d',
  compile2_flagged_declaration_f d = d' ->
    compile2_flagged_declaration d d'.
Proof.
  apply (declaration_ind
    (fun d: declaration => forall (d' : declaration_x),
      compile2_flagged_declaration_f d = d' ->
      compile2_flagged_declaration d d')
    (fun p: procedure_body => forall (p': procedure_body_x),
      compile2_flagged_procedure_body_f p = p' ->
      compile2_flagged_procedure_body p p')
    ); smack.
- constructor.
- constructor.
  apply compile2_flagged_type_declaration_f_correctness; auto.
- constructor.
  apply compile2_flagged_object_declaration_f_correctness; auto.
- constructor;
  smack.
- constructor;
  smack.
- constructor.
  apply compile2_flagged_aspect_specifications_f_correctness; auto.
  apply compile2_flagged_parameter_specifications_f_correctness; auto.
  smack.
  apply compile2_flagged_stmt_f_correctness; auto.
Qed.

Lemma compile2_flagged_procedure_declaration_f_correctness: forall p p',
  compile2_flagged_procedure_body_f p = p' ->
    compile2_flagged_procedure_body p p'.
Proof.
  intros;
  destruct p; smack;
  constructor;
  [ apply compile2_flagged_aspect_specifications_f_correctness |
    apply compile2_flagged_parameter_specifications_f_correctness |
    apply compile2_flagged_declaration_f_correctness |
    apply compile2_flagged_stmt_f_correctness 
  ]; auto.
Qed.


(** * Lemmas *)

Require Import X_SparkTactics.

Lemma procedure_components_rel: forall p p',
  compile2_flagged_procedure_body p p' ->
  compile2_flagged_parameter_specifications (procedure_parameter_profile p) (procedure_parameter_profile_x p') /\
  compile2_flagged_declaration (procedure_declarative_part p) (procedure_declarative_part_x p') /\
  compile2_flagged_stmt (procedure_statements p) (procedure_statements_x p').
Proof.
  intros.
  inversion H; smack.
Qed.












