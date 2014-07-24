Require Export language_flagged.
Require Export symboltable.

(* ***************************************************************
   generate and insert check flags into AST nodes according to the 
   run-time check rules;
   *************************************************************** *)

(** * Compile To Flagged Program *)
(** check flags for an expression not only depends on its operators, 
    but also depends on its context where it appears, e.g. if it's 
    used as an index, then Do_Range_Check should be set for it;
    in the following formalization, check_flags are the check flags
    that are enforced by the context of the expression;
*)

(*
  TODO: add some optimization to the checks generator:
  - range check for literal index can be removed, similarly, 
    overflow check and division check for literal can be optimized away;
  - range check for varialbe index, whose type is the same as index type,
    can be optimized away;
  - subtype T is Integer range 1 .. 10; subtype U is Integer range 2 .. 12; 
    X: T; Y: U;
    Y = X + 1; (the range check for this assignment can also be optimized away)
               (the overflow check can also be removed, as X + 1 is in the range of integer)
    Y = Y / (X + 1);
               (the division check can also be removed, as (X + 1) > 0 )
*)

Inductive compile2_flagged_exp: symboltable -> check_flags -> expression -> expression_x -> Prop :=
    | C2_Flagged_Literal: forall st checkflags ast_num l,
        compile2_flagged_exp st checkflags 
                             (E_Literal ast_num l) 
                             (E_Literal_X ast_num l checkflags)
    | C2_Flagged_Name: forall st checkflags n n_flagged ast_num,
        compile2_flagged_name st checkflags n n_flagged -> (* checkflags is passed into name expression *)
        compile2_flagged_exp st checkflags 
                             (E_Name ast_num n) 
                             (E_Name_X ast_num n_flagged nil)
    | C2_Flagged_Binary_Operation_O: forall op st e1 e1_flagged e2 e2_flagged checkflags ast_num,
        op = Plus \/ op = Minus \/ op = Multiply ->
        compile2_flagged_exp st nil e1 e1_flagged ->
        compile2_flagged_exp st nil e2 e2_flagged ->
        compile2_flagged_exp st checkflags
                             (E_Binary_Operation ast_num op e1 e2)
                             (E_Binary_Operation_X ast_num op e1_flagged e2_flagged (Do_Overflow_Check :: checkflags))
    | C2_Flagged_Binary_Operation_OD: forall op st e1 e1_flagged e2 e2_flagged checkflags ast_num,
        op = Divide ->
        compile2_flagged_exp st nil e1 e1_flagged ->
        compile2_flagged_exp st nil e2 e2_flagged ->
        compile2_flagged_exp st checkflags
                             (E_Binary_Operation ast_num op e1 e2)
                             (E_Binary_Operation_X ast_num op e1_flagged e2_flagged (Do_Division_Check :: Do_Overflow_Check :: checkflags))
    | C2_Flagged_Binary_Operation_Others: forall op st e1 e1_flagged e2 e2_flagged checkflags ast_num,
        op <> Plus ->
        op <> Minus ->
        op <> Multiply ->
        op <> Divide ->
        compile2_flagged_exp st nil e1 e1_flagged ->
        compile2_flagged_exp st nil e2 e2_flagged ->
        compile2_flagged_exp st checkflags
                             (E_Binary_Operation ast_num op e1 e2)
                             (E_Binary_Operation_X ast_num op e1_flagged e2_flagged checkflags)
    | C2_Flagged_Unary_Operation_O: forall op st e e_flagged checkflags ast_num,
        op = Unary_Minus ->
        compile2_flagged_exp st nil e e_flagged ->
        compile2_flagged_exp st checkflags
                             (E_Unary_Operation ast_num op e) 
                             (E_Unary_Operation_X ast_num op e_flagged (Do_Overflow_Check :: checkflags))
    | C2_Flagged_Unary_Operation_Others: forall op st e e_flagged checkflags ast_num,
        op <> Unary_Minus ->
        compile2_flagged_exp st nil e e_flagged ->
        compile2_flagged_exp st checkflags
                             (E_Unary_Operation ast_num op e) 
                             (E_Unary_Operation_X ast_num op e_flagged checkflags)

with compile2_flagged_name: symboltable -> check_flags -> name -> name_x -> Prop :=
    | C2_Flagged_Identifier: forall st checkflags ast_num x,
        compile2_flagged_name st checkflags 
                              (E_Identifier ast_num x) 
                              (E_Identifier_X ast_num x checkflags) 
    | C2_Flagged_Indexed_Component: forall st e e_flagged checkflags ast_num x_ast_num x,
        compile2_flagged_exp st (Do_Range_Check :: nil) e e_flagged ->
        compile2_flagged_name st checkflags
                              (E_Indexed_Component ast_num x_ast_num x e) 
                              (E_Indexed_Component_X ast_num x_ast_num x e_flagged checkflags) 
    | C2_Flagged_Selected_Component: forall st checkflags ast_num x_ast_num x f,
        compile2_flagged_name st checkflags 
                              (E_Selected_Component ast_num x_ast_num x f) 
                              (E_Selected_Component_X ast_num x_ast_num x f checkflags).

(**
   For In / Out parameters, whose type is an integer subtype, range check should be
   added when it's both copied into the called procedure and copied out the procedure,
   these two range checks should be performed before the procedure call and after the
   procedure returns; here we only put one range check flag and don't distinguish whether
   it's a range check for copied in or copied out procedure;
*)

Inductive compile2_flagged_args: symboltable -> list parameter_specification -> list expression -> list expression_x -> Prop :=
    | C2_Flagged_Args_Null: forall st,
        compile2_flagged_args st nil nil nil
    | C2_Flagged_Args_In: forall st param arg arg_flagged lparam larg larg_flagged,
        param.(parameter_mode) = In \/ param.(parameter_mode) = In_Out ->
        is_range_constrainted_type (param.(parameter_subtype_mark)) = false ->
        compile2_flagged_exp st nil arg arg_flagged ->
        compile2_flagged_args st lparam larg larg_flagged -> 
        compile2_flagged_args st (param :: lparam) (arg :: larg) (arg_flagged :: larg_flagged)
    | C2_Flagged_Args_In_R: forall st param arg arg_flagged lparam larg larg_flagged,
        param.(parameter_mode) = In \/ param.(parameter_mode) = In_Out ->
        is_range_constrainted_type (param.(parameter_subtype_mark)) = true ->
        compile2_flagged_exp st (Do_Range_Check :: nil) arg arg_flagged ->
        compile2_flagged_args st lparam larg larg_flagged -> 
        compile2_flagged_args st (param :: lparam) (arg :: larg) (arg_flagged :: larg_flagged)
    | C2_Flagged_Args_Out: forall st param ast_num t x_ast_num x_flagged lparam larg larg_flagged x,
        param.(parameter_mode) = Out ->
        fetch_exp_type ast_num st = Some t ->
        is_range_constrainted_type t = false ->
        compile2_flagged_exp st nil (E_Name ast_num (E_Identifier x_ast_num x)) x_flagged ->
        compile2_flagged_args st lparam larg larg_flagged -> 
        compile2_flagged_args st (param :: lparam) ((E_Name ast_num (E_Identifier x_ast_num x)) :: larg) (x_flagged :: larg_flagged)
    | C2_Flagged_Args_Out_R: forall st param ast_num t x_ast_num x_flagged lparam larg larg_flagged x,
        param.(parameter_mode) = Out ->
        fetch_exp_type ast_num st = Some t ->
        is_range_constrainted_type t = true ->
        compile2_flagged_exp st (Do_Range_Check :: nil) (E_Name ast_num (E_Identifier x_ast_num x)) x_flagged ->
        compile2_flagged_args st lparam larg larg_flagged -> 
        compile2_flagged_args st (param :: lparam) ((E_Name ast_num (E_Identifier x_ast_num x)) :: larg) (x_flagged :: larg_flagged).


Inductive compile2_flagged_stmt: symboltable -> statement -> statement_x -> Prop := 
    | C2_Flagged_Null: forall st,
        compile2_flagged_stmt st S_Null S_Null_X
    | C2_Flagged_Assignment: forall x st t x_flagged e e_flagged ast_num,
        fetch_exp_type (name_astnum x) st = Some t ->
        is_range_constrainted_type t = false ->        
        compile2_flagged_name st nil x x_flagged ->
        compile2_flagged_exp  st nil e e_flagged ->
        compile2_flagged_stmt st
                              (S_Assignment   ast_num x e) 
                              (S_Assignment_X ast_num x_flagged e_flagged)
    | C2_Flagged_Assignment_R: forall x st t x_flagged e e_flagged ast_num,
        fetch_exp_type (name_astnum x) st = Some t ->
        is_range_constrainted_type t = true ->
        compile2_flagged_name st nil x x_flagged ->
        compile2_flagged_exp  st (Do_Range_Check :: nil) e e_flagged ->
        compile2_flagged_stmt st
                              (S_Assignment   ast_num x e)
                              (S_Assignment_X ast_num x_flagged e_flagged)
    | C2_Flagged_If: forall e e_flagged c1 c1_flagged c2 c2_flagged st ast_num,
        compile2_flagged_exp  st nil e e_flagged ->
        compile2_flagged_stmt st c1 c1_flagged ->
        compile2_flagged_stmt st c2 c2_flagged ->
        compile2_flagged_stmt st
                              (S_If   ast_num e c1 c2) 
                              (S_If_X ast_num e_flagged c1_flagged c2_flagged)
    | C2_Flagged_While: forall e e_flagged c c_flagged st ast_num,
        compile2_flagged_exp  st nil e e_flagged ->
        compile2_flagged_stmt st c c_flagged ->
        compile2_flagged_stmt st 
                              (S_While_Loop   ast_num e c) 
                              (S_While_Loop_X ast_num e_flagged c_flagged)
    | C2_Flagged_Procedure_Call: forall p st n pb params args args_flagged ast_num p_ast_num,
        fetch_proc p st = Some (n, pb) ->
        procedure_parameter_profile pb = params ->
        compile2_flagged_args st params args args_flagged ->
        compile2_flagged_stmt st
                              (S_Procedure_Call   ast_num p_ast_num p args) 
                              (S_Procedure_Call_X ast_num p_ast_num p args_flagged)
    | C2_Flagged_Sequence: forall st c1 c1_flagged c2 c2_flagged ast_num,
        compile2_flagged_stmt st c1 c1_flagged ->
        compile2_flagged_stmt st c2 c2_flagged ->
        compile2_flagged_stmt st
                              (S_Sequence ast_num   c1 c2)
                              (S_Sequence_X ast_num c1_flagged c2_flagged).


Inductive compile2_flagged_type_declaration: type_declaration -> type_declaration_x -> Prop :=
    | C2_Flagged_Subtype_Decl: forall ast_num tn t l u,
        compile2_flagged_type_declaration (Subtype_Declaration   ast_num tn t (Range l u))
                                          (Subtype_Declaration_X ast_num tn t (Range_X l u))
    | C2_Flagged_Derived_Type_Decl: forall ast_num tn t l u,
        compile2_flagged_type_declaration (Derived_Type_Declaration   ast_num tn t (Range l u))
                                          (Derived_Type_Declaration_X ast_num tn t (Range_X l u))
    | C2_Flagged_Integer_Type_Decl: forall ast_num tn l u,
        compile2_flagged_type_declaration (Integer_Type_Declaration   ast_num tn (Range l u))
                                          (Integer_Type_Declaration_X ast_num tn (Range_X l u))
    | C2_Flagged_Array_Type_Decl: forall ast_num tn tm t,
        compile2_flagged_type_declaration (Array_Type_Declaration   ast_num tn tm t)
                                          (Array_Type_Declaration_X ast_num tn tm t)
    | C2_Flagged_Record_Type_Decl: forall ast_num tn fs,
        compile2_flagged_type_declaration (Record_Type_Declaration   ast_num tn fs) 
                                          (Record_Type_Declaration_X ast_num tn fs).

Inductive compile2_flagged_object_declaration: symboltable -> object_declaration -> object_declaration_x -> Prop :=
    | C2_Flagged_Object_Declaration_NoneInit: forall st ast_num x t,
        compile2_flagged_object_declaration st 
                                            (mkobject_declaration   ast_num x t None) 
                                            (mkobject_declaration_x ast_num x t None) 
    | C2_Flagged_Object_Declaration: forall st t e e_flagged ast_num x,
        is_range_constrainted_type t = false ->
        compile2_flagged_exp st nil e e_flagged ->
        compile2_flagged_object_declaration st 
                                            (mkobject_declaration   ast_num x t (Some e)) 
                                            (mkobject_declaration_x ast_num x t (Some e_flagged))
    | C2_Flagged_Object_Declaration_R: forall st t e e_flagged ast_num x,
        is_range_constrainted_type t = true ->
        compile2_flagged_exp st (Do_Range_Check :: nil) e e_flagged ->
        compile2_flagged_object_declaration st 
                                            (mkobject_declaration   ast_num x t (Some e)) 
                                            (mkobject_declaration_x ast_num x t (Some e_flagged)).

Inductive compile2_flagged_object_declarations: symboltable -> list object_declaration -> list object_declaration_x -> Prop :=
    | C2_Flagged_Object_Declarations_Null: forall st,
        compile2_flagged_object_declarations st nil nil 
    | C2_Flagged_Object_Declarations_List: forall st o o_flagged lo lo_flagged,
        compile2_flagged_object_declaration  st o o_flagged ->
        compile2_flagged_object_declarations st lo lo_flagged ->
        compile2_flagged_object_declarations st (o :: lo) (o_flagged :: lo_flagged).


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


Inductive compile2_flagged_declaration: symboltable -> declaration -> declaration_x -> Prop :=
    | C2_Flagged_D_Null_Declaration: forall st,
        compile2_flagged_declaration st D_Null_Declaration D_Null_Declaration_X
    | C2_Flagged_D_Type_Declaration: forall t t_flagged st ast_num,
        compile2_flagged_type_declaration t t_flagged ->
        compile2_flagged_declaration st
                                     (D_Type_Declaration   ast_num t) 
                                     (D_Type_Declaration_X ast_num t_flagged)
    | C2_Flagged_D_Object_Declaration: forall st o o_flagged ast_num,
        compile2_flagged_object_declaration st o o_flagged ->
        compile2_flagged_declaration st 
                                     (D_Object_Declaration   ast_num o)
                                     (D_Object_Declaration_X ast_num o_flagged) 
    | C2_Flagged_D_Procedure_Declaration: forall st p p_flagged ast_num,
        compile2_flagged_procedure_body st p p_flagged ->
        compile2_flagged_declaration st 
                                     (D_Procedure_Body   ast_num p)
                                     (D_Procedure_Body_X ast_num p_flagged) 
    | C2_Flagged_D_Seq_Declaration: forall st d1 d1_flagged d2 d2_flagged ast_num,
        compile2_flagged_declaration st d1 d1_flagged ->
        compile2_flagged_declaration st d2 d2_flagged ->
        compile2_flagged_declaration st 
                                     (D_Seq_Declaration   ast_num d1 d2) 
                                     (D_Seq_Declaration_X ast_num d1_flagged d2_flagged)

with compile2_flagged_procedure_body: symboltable -> procedure_body -> procedure_body_x -> Prop :=
       | C2_Flagged_Procedure_Declaration: forall params params_flagged st decls decls_flagged
                                                  stmt stmt_flagged ast_num p,
           compile2_flagged_parameter_specifications params params_flagged ->
           compile2_flagged_declaration st decls decls_flagged ->
           compile2_flagged_stmt st stmt stmt_flagged ->
           compile2_flagged_procedure_body st 
                                           (mkprocedure_body   ast_num p params decls stmt)
                                           (mkprocedure_body_x ast_num p params_flagged decls_flagged stmt_flagged).


(* ***************************************************************
                          Funtion Version
   *************************************************************** *)

(** * Translator Function To Insert Checks *)

Function compile2_flagged_exp_f (st: symboltable) (checkflags: check_flags) (e: expression): expression_x :=
  match e with
  | E_Literal ast_num l => 
        E_Literal_X ast_num l checkflags
  | E_Name ast_num n => 
      let n_flagged := compile2_flagged_name_f st checkflags n in
        E_Name_X ast_num n_flagged nil
  | E_Binary_Operation ast_num op e1 e2 =>
      let e1_flagged := compile2_flagged_exp_f st nil e1 in
      let e2_flagged := compile2_flagged_exp_f st nil e2 in
        match op with
        | Plus     => E_Binary_Operation_X ast_num op e1_flagged e2_flagged (Do_Overflow_Check :: checkflags)
        | Minus    => E_Binary_Operation_X ast_num op e1_flagged e2_flagged (Do_Overflow_Check :: checkflags)
        | Multiply => E_Binary_Operation_X ast_num op e1_flagged e2_flagged (Do_Overflow_Check :: checkflags)
        | Divide   => E_Binary_Operation_X ast_num op e1_flagged e2_flagged (Do_Division_Check :: Do_Overflow_Check :: checkflags)
        | _        => E_Binary_Operation_X ast_num op e1_flagged e2_flagged checkflags
        end
  | E_Unary_Operation ast_num op e => 
      let e_flagged := compile2_flagged_exp_f st nil e in
        match op with
        | Unary_Minus => E_Unary_Operation_X ast_num op e_flagged (Do_Overflow_Check :: checkflags)
        | _           => E_Unary_Operation_X ast_num op e_flagged checkflags
        end
  end

with compile2_flagged_name_f (st: symboltable) (checkflags: check_flags) (n: name): name_x :=
  match n with
  | E_Identifier ast_num x =>
        E_Identifier_X ast_num x checkflags
  | E_Indexed_Component ast_num x_ast_num x e =>
      let e_flagged := compile2_flagged_exp_f st (Do_Range_Check :: nil) e in
        E_Indexed_Component_X ast_num x_ast_num x e_flagged checkflags
  | E_Selected_Component ast_num x_ast_num x f =>
        E_Selected_Component_X ast_num x_ast_num x f checkflags
  end.


Function compile2_flagged_args_f (st: symboltable) (params: list parameter_specification) (args: list expression): option (list expression_x) :=
  match params, args with
  | nil, nil => Some nil
  | param :: params', arg :: args' =>
      match param.(parameter_mode) with
      | In | In_Out =>
        if is_range_constrainted_type (param.(parameter_subtype_mark)) then
          let arg_flagged := compile2_flagged_exp_f st (Do_Range_Check :: nil) arg in
            match compile2_flagged_args_f st params' args' with
            | Some args_flagged => Some (arg_flagged :: args_flagged)
            | None              => None
            end
        else
          let arg_flagged := compile2_flagged_exp_f st nil arg in
            match compile2_flagged_args_f st params' args' with
            | Some args_flagged => Some (arg_flagged :: args_flagged)
            | None              => None
            end 
      | Out =>
        match arg with
        | E_Name ast_num (E_Identifier x_ast_num x) =>
            match fetch_exp_type ast_num st with
            | Some t =>
                if is_range_constrainted_type t then
                  let x_flagged := compile2_flagged_exp_f st (Do_Range_Check :: nil) (E_Name ast_num (E_Identifier x_ast_num x)) in
                    match compile2_flagged_args_f st params' args' with
                    | Some args_flagged => Some (x_flagged :: args_flagged)
                    | None              => None
                    end 
                else
                  None
            | None => None
            end
        | _ => None
        end 
      end   
  | _, _ => None
  end.

Function compile2_flagged_stmt_f (st: symboltable) (c: statement): option statement_x :=
  match c with
  | S_Null => Some S_Null_X
  | S_Assignment ast_num x e =>
      match fetch_exp_type (name_astnum x) st with
      | Some t =>
          if is_range_constrainted_type t then
            let x_flagged := compile2_flagged_name_f st nil x in
            let e_flagged := compile2_flagged_exp_f  st (Do_Range_Check :: nil) e in
              Some (S_Assignment_X ast_num x_flagged e_flagged) 
          else
            let x_flagged := compile2_flagged_name_f st nil x in
            let e_flagged := compile2_flagged_exp_f  st nil e in
              Some (S_Assignment_X ast_num x_flagged e_flagged)
      | None   => None
      end
  | S_If ast_num e c1 c2 =>
      let e_flagged := compile2_flagged_exp_f st nil e in
        match compile2_flagged_stmt_f st c1 with
        | Some c1_flagged =>
            match compile2_flagged_stmt_f st c2 with
            | Some c2_flagged => Some (S_If_X ast_num e_flagged c1_flagged c2_flagged)
            | None            => None
            end
        | None            => None
        end
  | S_While_Loop ast_num e c =>
      let e_flagged := compile2_flagged_exp_f st nil e in
        match compile2_flagged_stmt_f st c with
        | Some c_flagged => Some (S_While_Loop_X ast_num e_flagged c_flagged)
        | None           => None
        end
  | S_Procedure_Call ast_num p_ast_num p args =>
      match fetch_proc p st with
      | Some (n, pb) => 
          match compile2_flagged_args_f st (procedure_parameter_profile pb) args with
          | Some args_flagged => Some (S_Procedure_Call_X ast_num p_ast_num p args_flagged)
          | None              => None
          end
      | None         => None
      end
  | S_Sequence ast_num c1 c2 =>
      match compile2_flagged_stmt_f st c1 with
      | Some c1_flagged =>
          match compile2_flagged_stmt_f st c2 with
          | Some c2_flagged => Some (S_Sequence_X ast_num c1_flagged c2_flagged)
          | None            => None
          end
      | None            => None
      end
  end.

Function compile2_flagged_type_declaration_f (t: type_declaration): type_declaration_x :=
  match t with
  | Subtype_Declaration ast_num tn t (Range l u) =>
      Subtype_Declaration_X ast_num tn t (Range_X l u)
  | Derived_Type_Declaration ast_num tn t (Range l u) =>
      Derived_Type_Declaration_X ast_num tn t (Range_X l u)
  | Integer_Type_Declaration ast_num tn (Range l u) =>
      Integer_Type_Declaration_X ast_num tn (Range_X l u)
  | Array_Type_Declaration ast_num tn tm t => 
      Array_Type_Declaration_X ast_num tn tm t
  | Record_Type_Declaration ast_num tn fs =>
      Record_Type_Declaration_X ast_num tn fs
  end.

Function compile2_flagged_object_declaration_f (st: symboltable) (o: object_declaration): object_declaration_x :=
  match o with
  | mkobject_declaration ast_num x t None =>
        mkobject_declaration_x ast_num x t None
  | mkobject_declaration ast_num x t (Some e) => 
      if is_range_constrainted_type t then
        let e_flagged := compile2_flagged_exp_f st (Do_Range_Check :: nil) e in
          mkobject_declaration_x ast_num x t (Some e_flagged) 
      else
        let e_flagged := compile2_flagged_exp_f st nil e in
          mkobject_declaration_x ast_num x t (Some e_flagged)
  end.

Function compile2_flagged_object_declarations_f (st: symboltable) (lo: list object_declaration): list object_declaration_x :=
  match lo with
  | nil => nil
  | o :: lo' => 
      let o_flagged  := compile2_flagged_object_declaration_f st o in
      let lo_flagged := compile2_flagged_object_declarations_f st lo' in
        o_flagged :: lo_flagged
  end.

Function compile2_flagged_parameter_specification_f (param: parameter_specification): parameter_specification_x :=
  match param with
  | mkparameter_specification ast_num x t m =>
      mkparameter_specification_x ast_num x t m
  end.

Function compile2_flagged_parameter_specifications_f (lparam: list parameter_specification): list parameter_specification_x :=
  match lparam with
  | nil => nil
  | param :: lparam' =>
      let param_flagged := compile2_flagged_parameter_specification_f param in
      let lparam_flagged := compile2_flagged_parameter_specifications_f lparam' in
        param_flagged :: lparam_flagged
  end.


Function compile2_flagged_declaration_f (st: symboltable) (d: declaration): option declaration_x :=
  match d with
  | D_Null_Declaration => Some D_Null_Declaration_X
  | D_Type_Declaration ast_num t =>
      let t_flagged := compile2_flagged_type_declaration_f t in
        Some (D_Type_Declaration_X ast_num t_flagged)
  | D_Object_Declaration ast_num o =>
      let o_flagged := compile2_flagged_object_declaration_f st o in
        Some (D_Object_Declaration_X ast_num o_flagged)
  | D_Procedure_Body ast_num p =>
      match compile2_flagged_procedure_body_f st p with
      | Some p_flagged => Some (D_Procedure_Body_X ast_num p_flagged)
      | None           => None
      end
  | D_Seq_Declaration ast_num d1 d2 =>
      match compile2_flagged_declaration_f st d1 with
      | Some d1_flagged =>
          match compile2_flagged_declaration_f st d2 with
          | Some d2_flagged => Some (D_Seq_Declaration_X ast_num d1_flagged d2_flagged)
          | None            => None
          end
      | None                => None
      end
  end

with compile2_flagged_procedure_body_f (st: symboltable) (p: procedure_body): option procedure_body_x :=
  match p with
  | mkprocedure_body ast_num p params decls stmt =>
      let params_flagged := compile2_flagged_parameter_specifications_f params in
        match compile2_flagged_declaration_f st decls with
        | Some decls_flagged =>
          match compile2_flagged_stmt_f st stmt with
          | Some stmt_flagged => Some (mkprocedure_body_x ast_num p params_flagged decls_flagged stmt_flagged)
          | None              => None
          end
        | None                => None
        end
  end.


(* ***************************************************************
                 Semantics Equivalence Proof
   *************************************************************** *)

(** * Semantics Equivalence Proof For Translator *)

Scheme expression_ind := Induction for expression Sort Prop 
                         with name_ind := Induction for name Sort Prop.

Lemma compile2_flagged_exp_f_correctness: forall e e' checkflags st,
  compile2_flagged_exp_f st checkflags e = e' ->
    compile2_flagged_exp st checkflags e e'.
Proof.
  apply (expression_ind
    (fun e: expression => forall (e' : expression_x) (checkflags: check_flags) (st: symboltable),
      compile2_flagged_exp_f st checkflags e = e' ->
      compile2_flagged_exp   st checkflags e e')
    (fun n: name => forall (n': name_x) (checkflags: check_flags) (st: symboltable),
      compile2_flagged_name_f st checkflags n = n' ->
      compile2_flagged_name   st checkflags n n')
    ); smack;
  [ | | 
    destruct b; constructor; smack | 
    destruct u; constructor; smack | | | 
  ];
  constructor; apply H; auto.
Qed.

Lemma compile2_flagged_name_f_correctness: forall st checkflags n n',
  compile2_flagged_name_f st checkflags n = n' ->
    compile2_flagged_name st checkflags n n'.
Proof.
  intros.
  destruct n; smack;
  repeat progress constructor;
  apply compile2_flagged_exp_f_correctness; auto.
Qed.

Lemma compile2_flagged_args_f_correctness: forall st params args args',
  compile2_flagged_args_f st params args = Some args' ->
    compile2_flagged_args st params args args'.
Proof.
  induction params; smack.
- destruct args; smack.
  constructor.
- destruct args; smack.
  remember (parameter_mode a) as m;
  remember (is_range_constrainted_type (parameter_subtype_mark a)) as x;
  remember (compile2_flagged_args_f st params args) as y;
  destruct m, x, y; smack;

  [apply C2_Flagged_Args_In_R; smack |
   apply C2_Flagged_Args_In; smack | | | | |
   apply C2_Flagged_Args_In_R; smack |
   apply C2_Flagged_Args_In; smack 
  ]; 
  try (apply compile2_flagged_exp_f_correctness; auto);

  destruct e; smack; destruct n; smack;
  remember (fetch_exp_type a0 st) as x;
  destruct x; smack;
  remember (is_range_constrainted_type t) as y;
  destruct y; smack;
  
  apply C2_Flagged_Args_Out_R with (t := t); auto;
  apply compile2_flagged_exp_f_correctness; auto.
Qed.
  
Lemma compile2_flagged_stmt_f_correctness: forall st c c',
  compile2_flagged_stmt_f st c = Some c' ->
    compile2_flagged_stmt st c c'.
Proof.
  induction c; smack.
- constructor.
- remember (fetch_exp_type (name_astnum n) st) as x;
  destruct x; smack.
  remember (is_range_constrainted_type t) as y.
  destruct y; smack;
  [apply C2_Flagged_Assignment_R with (t := t); smack |
   apply C2_Flagged_Assignment with (t := t); smack 
  ];
  [apply compile2_flagged_name_f_correctness; auto | | 
   apply compile2_flagged_name_f_correctness; auto | 
  ];
  apply compile2_flagged_exp_f_correctness; auto.
- remember (compile2_flagged_stmt_f st c1) as x;
  destruct x; smack.
  remember (compile2_flagged_stmt_f st c2) as y;
  destruct y; smack.
  constructor;
  [ apply compile2_flagged_exp_f_correctness | | ];
  smack.
- remember (compile2_flagged_stmt_f st c) as x;
  destruct x; smack.
  constructor;
  [ apply compile2_flagged_exp_f_correctness | ];
  smack.
- remember (fetch_proc p st) as x;
  destruct x; smack.
  destruct t.
  remember (compile2_flagged_args_f st (procedure_parameter_profile p0) l) as y;
  destruct y; smack.
  apply C2_Flagged_Procedure_Call with (n := l0) (pb := p0) (params := (procedure_parameter_profile p0)); smack.
  apply compile2_flagged_args_f_correctness; auto.
- remember (compile2_flagged_stmt_f st c1) as x;
  destruct x; smack.
  remember (compile2_flagged_stmt_f st c2) as y;
  destruct y; smack.
  constructor; auto.
Qed.

Lemma compile2_flagged_type_declaration_f_correctness: forall t t',
  compile2_flagged_type_declaration_f t = t' ->
      compile2_flagged_type_declaration t t'.
Proof.
  destruct t; smack;
  try (destruct r); constructor.
Qed.

Lemma compile2_flagged_object_declaration_f_correctness: forall st o o',
  compile2_flagged_object_declaration_f st o = o' ->
    compile2_flagged_object_declaration st o o'.
Proof.
  intros;
  functional induction compile2_flagged_object_declaration_f st o; smack;
  [constructor |
   apply C2_Flagged_Object_Declaration_R; auto |
   apply C2_Flagged_Object_Declaration; auto
  ];
  apply compile2_flagged_exp_f_correctness; auto.
Qed.

Lemma compile2_flagged_object_declarations_f_correctness: forall st lo lo',
  compile2_flagged_object_declarations_f st lo = lo' ->
    compile2_flagged_object_declarations st lo lo'.
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


Scheme declaration_ind := Induction for declaration Sort Prop 
                          with procedure_body_ind := Induction for procedure_body Sort Prop.

Lemma compile2_flagged_declaration_f_correctness: forall d d' st,
  compile2_flagged_declaration_f st d = Some d' ->
    compile2_flagged_declaration st d d'.
Proof.
  apply (declaration_ind
    (fun d: declaration => forall (d' : declaration_x) (st: symboltable),
      compile2_flagged_declaration_f st d = Some d' ->
      compile2_flagged_declaration st d d')
    (fun p: procedure_body => forall (p': procedure_body_x) (st: symboltable),
      compile2_flagged_procedure_body_f st p = Some p' ->
      compile2_flagged_procedure_body st p p')
    ); smack.
- constructor.
- constructor.
  apply compile2_flagged_type_declaration_f_correctness; auto.
- constructor.
  apply compile2_flagged_object_declaration_f_correctness; auto.
- remember (compile2_flagged_procedure_body_f st p) as x; 
  destruct x; smack.
  constructor; auto.
- remember (compile2_flagged_declaration_f st d) as x;
  remember (compile2_flagged_declaration_f st d0) as y;
  destruct x, y; smack.  
  constructor; smack.
- remember (compile2_flagged_declaration_f st procedure_declarative_part) as x;
  remember (compile2_flagged_stmt_f st procedure_statements) as y;
  destruct x, y; smack.
  constructor;
  [ apply compile2_flagged_parameter_specifications_f_correctness | |
    apply compile2_flagged_stmt_f_correctness
  ]; auto.
Qed.

Lemma compile2_flagged_procedure_declaration_f_correctness: forall st p p',
  compile2_flagged_procedure_body_f st p = Some p' ->
    compile2_flagged_procedure_body st p p'.
Proof.
  intros;
  destruct p; smack.
  remember (compile2_flagged_declaration_f st procedure_declarative_part) as x;
  remember (compile2_flagged_stmt_f st procedure_statements) as y;
  destruct x, y; smack.  
  constructor;
  [ apply compile2_flagged_parameter_specifications_f_correctness |
    apply compile2_flagged_declaration_f_correctness |
    apply compile2_flagged_stmt_f_correctness 
  ]; auto.
Qed.


(** * Lemmas *)

Require Import X_SparkTactics.

Lemma procedure_components_rel: forall st p p',
  compile2_flagged_procedure_body st p p' ->
  compile2_flagged_parameter_specifications (procedure_parameter_profile p) (procedure_parameter_profile_x p') /\
  compile2_flagged_declaration st (procedure_declarative_part p) (procedure_declarative_part_x p') /\
  compile2_flagged_stmt st (procedure_statements p) (procedure_statements_x p').
Proof.
  intros.
  inversion H; smack.
Qed.


(** * Compile To Flagged Symbol Table *)


Inductive compile2_flagged_proc_declaration_map: symboltable ->
                                                 list (idnum * (level * procedure_body)) -> 
                                                 list (idnum * (level * procedure_body_x)) -> Prop :=
    | C2_Flagged_Proc_Declaration_Map_Null: forall st,
        compile2_flagged_proc_declaration_map st nil nil
    | C2_Flagged_Proc_Declaration_Map: forall st pb pb' pl pl' p l,
        compile2_flagged_procedure_body st pb pb' ->
        compile2_flagged_proc_declaration_map st pl pl' ->
        compile2_flagged_proc_declaration_map st ((p, (l, pb)) :: pl) ((p, (l, pb')) :: pl').

Inductive compile2_flagged_type_declaration_map: list (idnum * type_declaration) -> 
                                                 list (idnum * type_declaration_x) -> Prop :=
    | C2_Flagged_Type_Declaration_Map_Null:
        compile2_flagged_type_declaration_map nil nil
    | C2_Flagged_Type_Declaration_Map: forall t t' tl tl' x,
        compile2_flagged_type_declaration t t' ->
        compile2_flagged_type_declaration_map tl tl' ->
        compile2_flagged_type_declaration_map ((x, t) :: tl) ((x, t') :: tl').

Inductive compile2_flagged_symbol_table: symboltable -> symboltable_x -> Prop := 
  | C2_Flagged_SymTable: forall p p' t t' x e,
      compile2_flagged_proc_declaration_map (mkSymbolTable x p t e) p p' ->
      compile2_flagged_type_declaration_map t t' ->
      compile2_flagged_symbol_table (mkSymbolTable x p t e) (mkSymbolTable_x x p' t' e).


(** ** Lemmas *)

Lemma procedure_declaration_rel: forall st ps ps' p n pb n' pb',
  compile2_flagged_proc_declaration_map st ps ps' ->
    Symbol_Table_Module.SymTable_Procs.fetches p ps = Some (n, pb) ->
      Symbol_Table_Module_X.SymTable_Procs.fetches p ps' = Some (n', pb') ->
        n = n' /\ compile2_flagged_procedure_body st pb pb'.
Proof.
  intros st ps ps' p n pb n' pb' H; revert p n pb n' pb'.
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
        n = n' /\ compile2_flagged_procedure_body st pb pb'.
Proof.
  intros.
  inversion H1; subst; clear H1.
  unfold Symbol_Table_Module_X.fetch_proc in H0;
  unfold Symbol_Table_Module.fetch_proc in H;
  simpl in H0, H.
  specialize (procedure_declaration_rel _ _ _ _ _ _ _ _ H2 H H0);
  auto.
Qed.

