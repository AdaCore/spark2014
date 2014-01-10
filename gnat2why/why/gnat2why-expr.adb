------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                        G N A T 2 W H Y - E X P R                         --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                       Copyright (C) 2010-2014, AdaCore                   --
--                                                                          --
-- gnat2why is  free  software;  you can redistribute  it and/or  modify it --
-- under terms of the  GNU General Public License as published  by the Free --
-- Software  Foundation;  either version 3,  or (at your option)  any later --
-- version.  gnat2why is distributed  in the hope that  it will be  useful, --
-- but WITHOUT ANY WARRANTY; without even the implied warranty of  MERCHAN- --
-- TABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public --
-- License for  more details.  You should have  received  a copy of the GNU --
-- General  Public License  distributed with  gnat2why;  see file COPYING3. --
-- If not,  go to  http://www.gnu.org/licenses  for a complete  copy of the --
-- license.                                                                 --
--                                                                          --
-- gnat2why is maintained by AdaCore (http://www.adacore.com)               --
--                                                                          --
------------------------------------------------------------------------------

--  For debugging, to print info on the output before raising an exception
with Ada.Text_IO;

with GNAT.Source_Info;

with Ada.Containers;         use Ada.Containers;

with Atree;                  use Atree;
with Einfo;                  use Einfo;
with Errout;                 use Errout;
with Eval_Fat;
with Namet;                  use Namet;
with Nlists;                 use Nlists;
with Opt;
with Sem_Aux;                use Sem_Aux;
with Sem_Eval;               use Sem_Eval;
with Sem_Util;               use Sem_Util;
with Sinfo;                  use Sinfo;
with Sinput;                 use Sinput;
with Snames;                 use Snames;
with Stand;                  use Stand;
with Uintp;                  use Uintp;
with Urealp;                 use Urealp;

with SPARK_Frame_Conditions; use SPARK_Frame_Conditions;
with SPARK_Util;             use SPARK_Util;

with VC_Kinds;               use VC_Kinds;

with Flow_Types;             use Flow_Types;
with Flow.Utility;           use Flow.Utility;

with Why;                    use Why;
with Why.Unchecked_Ids;      use Why.Unchecked_Ids;
with Why.Atree.Builders;     use Why.Atree.Builders;
with Why.Atree.Accessors;    use Why.Atree.Accessors;
with Why.Atree.Mutators;     use Why.Atree.Mutators;
with Why.Atree.Modules;      use Why.Atree.Modules;
with Why.Conversions;        use Why.Conversions;
with Why.Gen.Arrays;         use Why.Gen.Arrays;
with Why.Gen.Binders;        use Why.Gen.Binders;
with Why.Gen.Decl;           use Why.Gen.Decl;
with Why.Gen.Expr;           use Why.Gen.Expr;
with Why.Gen.Names;          use Why.Gen.Names;
with Why.Gen.Progs;          use Why.Gen.Progs;
with Why.Gen.Records;        use Why.Gen.Records;
with Why.Gen.Terms;          use Why.Gen.Terms;
with Why.Gen.Preds;          use Why.Gen.Preds;
with Why.Inter;              use Why.Inter;

with Gnat2Why.Decls;         use Gnat2Why.Decls;
with Gnat2Why.Expr.Loops;    use Gnat2Why.Expr.Loops;
with Gnat2Why.Subprograms;   use Gnat2Why.Subprograms;

package body Gnat2Why.Expr is

   --  This package handles the translation of expressions and statements to
   --  Why.

   --  -----------------------------
   --  Handling of 'Image and 'Value
   --  -----------------------------
   --
   --  For each scalar type, we introduce functions corresponding to 'Image and
   --  'Value. Logically, the return type of 'Image and the argument type of
   --  'Value should be Standard__String, but this would be circular, as String
   --  depends on a scalar type itself. Therefore, we introduce an abstract
   --  type __image, which is used as return type/argument type of the Why3
   --  functions for 'Image and 'Value. In addition, in the Why3 module for
   --  Standard__String, we generate two conversion functions between __image
   --  and String. The actual translation of the attributes now needs to use
   --  these conversion functions to get an actual String from a scalar, or
   --  to be able to convert a string to a scalar. So X'Image gets converted to
   --
   --  Standard__String.to_string (attr__ATTRIBUTE_IMAGE (to_int (x)))
   --
   --  Finally, to express that 'Value may fail, there is also a program
   --  function that corresponds to 'Value, that has an unprovable
   --  precondition, and "true" as postcondition.

   --  Code pointers:
   --    * Why3 declarations for type __image and the attributes Image
   --      and Value: see file ada__model.mlw.
   --    * Special case for the Standard__String module: see
   --      why-gen-arrays.adb:Declare_Unconstrained_Array
   --    * handling of the attributes: Transform_Attr in this file.

   -----------------------
   -- Local Subprograms --
   -----------------------

   function Apply_Modulus_Or_Rounding
      (E                     : Entity_Id;
       T                     : W_Expr_Id;
       Domain                : EW_Domain)
       return W_Expr_Id;
   --  If E is a modular type, apply a modulus on T. If E is a single or
   --  double precision floating-point type, apply the corresponding
   --  rounding operation. If E is neither, return T unchanged.

   function Insert_Overflow_Check
     (Ada_Node : Node_Id;
      T        : W_Expr_Id;
      In_Type  : Entity_Id) return W_Expr_Id
     with Pre => Is_Scalar_Type (In_Type);
   --  Inserts an overflow check on top of the Why expression T, using the
   --  bounds of the base type of In_Type. Use Ada_Node for the VC location.

   function Case_Expr_Of_Ada_Node
     (N             : Node_Id;
      Expected_Type : W_Type_OId := Why_Empty;
      Domain        : EW_Domain;
      Params        : Transformation_Params) return W_Expr_Id;
   --  Build Case expression of Ada Node.

   function Compute_Call_Args
     (Call        : Node_Id;
      Domain      : EW_Domain;
      Nb_Of_Refs  : out Natural;
      Params      : Transformation_Params) return W_Expr_Array;
   --  Compute arguments for a function call or procedure call. The node in
   --  argument must have a "Name" field and a "Parameter_Associations" field.
   --  Nb_Of_Refs is the number of ref arguments that could not be
   --  translated "as is" (because of a type mismatch) and for which
   --  Insert_Ref_Context must be called.

   function Why_Subp_Has_Precondition (E : Entity_Id) return Boolean;
   --  Return true whenever the Why declaration that corresponds to the given
   --  subprogram has a precondition.

   function Discrete_Choice_Is_Range (Choice : Node_Id) return Boolean;
   --  Return whether Choice is a range ("others" counts as a range)

   function Needs_Temporary_Ref
     (Actual : Node_Id;
      Formal : Node_Id)
     return Boolean;
   --  True if the parameter passing needs a temporary ref to be performed.

   function Insert_Ref_Context
     (Params     : Transformation_Params;
      Ada_Call   : Node_Id;
      Why_Call   : W_Prog_Id;
      Nb_Of_Refs : Positive) return W_Prog_Id;
   --  Considering a call to an Ada subprogram; Ada_Call being its node
   --  in the Ada syntax tree, and Why_Call its corresponding call in the
   --  Why syntax tree:
   --
   --  For all "out"/"in out" parameters that need a conversion, generate
   --  the whole context around the call, using a temporary variable
   --  which is named after the corresponding formal. e.g. something of the
   --  form:
   --
   --   let formal := ref (to_formal_type_ (from_actual_type (!actual))) in
   --    (<why_call> ;
   --     actual := to_actual_type_ (from_formal_type (!formal))
   --
   --  Nb_Of_Refs should be set to the number of such parameters in Ada_Call.

   function Is_Pretty_Node (N : Node_Id) return Boolean;
   --  Decide whether this is a node where we should put a pretty printing
   --  label, or if we should descend further

   function One_Level_Access
     (N           : Node_Id;
      Expr        : W_Expr_Id;
      Domain      : EW_Domain;
      Params      : Transformation_Params) return W_Expr_Id;
   --  Compute an access expression for record and array accesses without
   --  considering subexpressions. [N] represents the Ada node of the access,
   --  and [Expr] the Why expression of the prefix.

   function One_Level_Update
     (N           : Node_Id;
      Pref        : W_Expr_Id;
      Value       : W_Expr_Id;
      Domain      : EW_Domain;
      Params      : Transformation_Params) return W_Expr_Id;
   --  same as One_Level_Access, but for updates

   function Expected_Type_Of_Prefix (N : Node_Id) return W_Type_Id;
   --  The node in argument is the target of an assignment. This function
   --  computes the type of the entity that corresponds to the access.
   --  This may be different from the Etype of the node in case of
   --  unconstrained array types, or discriminant records.

   function Transform_Block_Statement (N : Node_Id) return W_Prog_Id;

   function Transform_Discrete_Choice
     (Choice      : Node_Id;
      Choice_Type : Entity_Id;
      Expr        : W_Expr_Id;
      Domain      : EW_Domain;
      Params      : Transformation_Params) return W_Expr_Id;
   --  For an expression Expr of a type EW_Int and a discrete Choice, build
   --  the expression that Expr belongs to the range expressed by Choice. In
   --  programs, also generate a check that dynamic choices are in the subtype
   --  Choice_Type.

   function Transform_Identifier (Params       : Transformation_Params;
                                  Expr         : Node_Id;
                                  Ent          : Entity_Id;
                                  Domain       : EW_Domain)
                                  return W_Expr_Id;
   --  Transform an Ada identifier to a Why item (take care of enumeration
   --  literals, boolean values etc)
   --
   --  This also deals with volatility, so that an object with a Async_Writers
   --  is suitably havoc'd before being read.

   function Transform_Quantified_Expression
     (Expr   : Node_Id;
      Domain : EW_Domain;
      Params : Transformation_Params) return W_Expr_Id;

   function Transform_Declaration (Decl : Node_Id) return W_Prog_Id;
   --  Transform a declaration. Return a program that takes into account the
   --  dynamic semantics of the declaration (checks and assumptions).

   function Transform_Statement_Or_Declaration
     (Stmt_Or_Decl   : Node_Id;
      Assert_And_Cut : out W_Pred_Id) return W_Prog_Id;
   --  Transform the Ada statement into a Why program expression.
   --  If Assert_And_Cut is not Why_Empty, the statement was a "pragma
   --  Assert_And_Cut". In this case, Assert_And_Cut contains the
   --  Why3 predicate equivalent of the assertion expression, and
   --  Transform_Statement contains the check program expression
   --  that corresponds to the assertion expression.

   function Transform_Aggregate
     (Params              : Transformation_Params;
      Domain              : EW_Domain;
      Expr                : Node_Id;
      In_Attribute_Update : Boolean := False) return W_Expr_Id;
   --  Transform an aggregate Expr. It may be called multiple times on the
   --  same Ada node, corresponding to different phases of the translation. The
   --  first time it is called on an Ada node, a logic function is generated
   --  and stored in Ada_To_Why_Func, so that the function and axiom are
   --  generated only once per source aggregate. This function F is used
   --  for generating each translation of this node. The general signature for
   --  F  is:
   --
   --     function F (<params>) : <type of aggregate>
   --
   --     axiom A:
   --        forall R:<type of aggregate>. forall <params>.
   --           R = F(<params>) -> <proposition for the aggregate R>
   --
   --  F takes as in parameters all components passed to the aggregate.
   --  This is simply the list of components for a one-dimensional aggregate,
   --  and it takes into account sub-components for multi-dimensional
   --  aggregates.
   --
   --  ( On the aggregate (1 => X, others => Y), components are {X, Y}.
   --  On the aggregate (1 => (1 => X, others => Y), 2 => Z), components are
   --  {X, Y, Z}.)
   --
   --  In_Attribute_Update is True for an aggregate used as argument of a
   --  'Update attribute_reference, and False for a regular aggregate.
   --
   --  If In_Attribute_Update is True, there are some additional properties for
   --  the logic function created (F):
   --
   --    a) the prefix array is sent as an extra parameter. "Others" is not
   --       allowed so no parameter for that, instead the values from the
   --       prefix array are used.
   --
   --    b) an extra parameter for every choice, since they can be dynamic,
   --       and an extra pair of parameters for each choice range (high and
   --       low range bounds).
   --
   --    c) the order of the cases in the generated why if statement in the
   --       axiom for the logic function needs to be the _reverse_ of that
   --       given in the aggregate, because associations can duplicate indices,
   --       and the prefix should be updated in the order the associations and
   --       choices are given.
   --
   --  As an example:
   --  Arr'Update(1 .. 3 => 10, 2 => 20, 2 .. 4 => 30, 3 => 40));
   --  is allowed for an array and should mean
   --  Arr(1) = 10 and Arr(2) = 30 and Arr(3) = 40 and Arr(4) = 30

   function Transform_Slice
     (Params       : Transformation_Params;
      Domain       : EW_Domain;
      Expr         : Node_Id) return W_Expr_Id;
   --  Transform a slice Expr.

   function Transform_Concatenation
     (Params : Transformation_Params;
      Domain : EW_Domain;
      Expr   : Node_Id) return W_Expr_Id;
   --  Handle concatenation nodes

   function Transform_Assignment_Statement (Stmt : Node_Id) return W_Prog_Id;
   --  Translate a single Ada statement into a Why expression

   function New_Assignment
     (Ada_Node : Node_Id := Empty;
      Lvalue   : Node_Id;
      Expr     : W_Prog_Id) return W_Prog_Id;
   --  Translate an assignment of the form "Lvalue := Expr",
   --  using Ada_Node for its source location.

   ------------------------------------------
   -- Handling of Expressions with Actions --
   ------------------------------------------

   --  The detection phase currently allows 3 kinds of nodes in actions:
   --    N_Object_Declaration for constants
   --    N_Subtype_Declaration
   --    N_Full_Type_Declaration

   --  Declarations of constant objects are transformed into let-binding in
   --  Why, which is possible in any context (program, term, proposition).

   --  Declarations of types are simply ignored. Indeed, we don't know how to
   --  translate the assignment to type bounds like done in
   --  Transform_Declaration in a proposition context. Note that this choice
   --  can possibly lead to dynamic bounds not known at VC level, if such types
   --  are introduced in actions.

   function Transform_Actions
     (Actions : List_Id;
      Expr    : W_Expr_Id;
      Domain  : EW_Domain;
      Params  : Transformation_Params) return W_Expr_Id;
   --  Translate a list of Actions, that should consist only in declarations of
   --  constants used in Expr.

   procedure Transform_Actions_Preparation (Actions : List_Id);
   --  Update the symbol table for taking into account the names for
   --  declarations of constants in Actions.

   function Transform_Attr
     (Expr               : Node_Id;
      Domain             : EW_Domain;
      Params             : Transformation_Params) return W_Expr_Id;
   --  Range_Check_Needed is set to True for some attributes (like 'Pos,
   --  'Length, 'Modulus) which return a universal integer, so that we check
   --  the result fits in the actual type used for the node.

   procedure Transform_String_Literal
     (Params : Transformation_Params;
      N      : Node_Id);
   --  Create an uninterpreted logic function with no parameters that returns a
   --  string value corresponding to the string literal.

   function Transform_Record_Component_Associations
     (Domain              : EW_Domain;
      Typ                 : Entity_Id;
      Assocs              : List_Id;
      Params              : Transformation_Params;
      In_Attribute_Update : Boolean := False) return W_Field_Association_Array;
   --  Returns a list of updates to be applied to a record value, to
   --  translate either an aggregate or a reference to attribute Update.
   --  In_Attribute_Update is True when translating a reference to attribute
   --  Update.

   function Transform_Binop (Op : N_Binary_Op) return EW_Binary_Op;
   --  Convert an Ada binary operator to a Why term symbol

   function Transform_Enum_Literal
     (Expr         : Node_Id;
      Enum         : Entity_Id;
      Domain       : EW_Domain)
      return W_Expr_Id;
   --  Translate an Ada enumeration literal to Why.

   function Transform_Compare_Op (Op : N_Op_Compare) return EW_Relation;
   --  Convert an Ada comparison operator to a Why relation symbol

   function Transform_Membership_Expression
     (Params : Transformation_Params;
      Domain : EW_Domain;
      Expr   : Node_Id) return W_Expr_Id;
   --  Convert a membership expression (N_In or N_Not_In) into a boolean Why
   --  expression.

   function Transform_Pragma (Prag : Node_Id) return W_Prog_Id with
     Pre => Nkind (Prag) = N_Pragma;
   --  Returns the Why program for pragma Prag

   function Transform_Pragma_Check (Prag : Node_Id) return W_Prog_Id;
   --  Returns the Why program for pragma Check (pragma Assert,
   --  Assume etc internally are all pragma Check).

   function Transform_Array_Equality
     (Params : Transformation_Params;
      Expr   : Node_Id;
      Domain : EW_Domain) return W_Expr_Id;
   --  Translate an equality on arrays into a Why expression, take care of the
   --  different cases (constrained / unconstrained) for each argument

   function Transform_Array_Comparison
     (Params : Transformation_Params;
      Expr   : Node_Id;
      Domain : EW_Domain) return W_Expr_Id;
   --  Translate a comparison on arrays into a Why expression

   function Transform_Array_Logical_Op
     (Params   : Transformation_Params;
      Expr     : Node_Id;
      Domain   : EW_Domain;
      Do_Check : Boolean) return W_Expr_Id;
   --  Translate a binary operation on boolean arrays into a Why expression

   function Transform_Array_Negation
     (Params   : Transformation_Params;
      Expr     : Node_Id;
      Domain   : EW_Domain;
      Do_Check : Boolean) return W_Expr_Id;
   --  Translate negation on boolean arrays into a Why expression

   function Transform_Raise (Stat : Node_Id) return W_Prog_Id with
     Pre => Nkind (Stat) in N_Raise_xxx_Error | N_Raise_Statement;
   --  Returns the Why program for raise statement Stat

   -------------------
   -- Apply_Modulus --
   -------------------

   function Apply_Modulus_Or_Rounding
      (E                     : Entity_Id;
       T                     : W_Expr_Id;
       Domain                : EW_Domain)
      return W_Expr_Id
   is
   begin
      if Is_Modular_Integer_Type (E) then
         return
            New_Call (Name => Integer_Math_Mod,
                      Domain => Domain,
                      Args =>
                       (1 => T,
                        2 => New_Integer_Constant
                          (Value => Modulus (E))),
                      Typ  => EW_Int_Type);

      --  Currently apply rounding on both floating-point and fixed-point
      --  types. The rounding on fixed-point types is an uninterpreted and
      --  unaxiomatized function, which models soundly (if not accurately)
      --  the semantics of fixed-point numbers.

      elsif Is_Floating_Point_Type (E)
              or else
            Is_Fixed_Point_Type (E)
      then
         return New_Call (Domain   => Domain,
                          Name     => Float_Round_Name (E),
                          Args     => (1 => T),
                          Typ      => EW_Real_Type);

      else
         return T;
      end if;
   end Apply_Modulus_Or_Rounding;

   ----------------------------
   -- Assignment_Of_Obj_Decl --
   ----------------------------

   function Assignment_Of_Obj_Decl (N : Node_Id) return W_Prog_Id
   is
      Lvalue   : Entity_Id := Defining_Identifier (N);
      Rexpr    : constant Node_Id := Expression (N);
   begin

      --  In our Why translation, all objects are declared at top-level.
      --  Object declarations in Ada inside Subprograms are therefore
      --  translated to assignments to initialize these objects.
      --  We can only generate an assignment when the Lvalue is mutable; if it
      --  is not, there are two cases. If the expression is static, we already
      --  have generated an axiom upon declaration of the object, and we are
      --  done. If it is not, we replace the assignment by an assumption of
      --  the following form:

      --  let var_name__assume = <rexpr> in
      --    assume (var_name = var_name_assume);

      --  Some objects have two declarations, e.g. the partial and full view of
      --  a package level object. In this case, we always use the type of the
      --  partial view.

      if Is_Full_View (Lvalue) then
         Lvalue := Partial_View (Lvalue);
      end if;

      if Present (Rexpr) then
         declare
            Why_Expr : constant W_Prog_Id :=
                         +Transform_Expr (Rexpr,
                                          EW_Abstract (Etype (Lvalue)),
                                          EW_Prog,
                                          Params => Body_Params);
            L_Name   : constant String := Full_Name (Lvalue);
            L_Id     : constant W_Identifier_Id := To_Why_Id (Lvalue);
         begin
            if Is_Mutable_In_Why (Lvalue) then
               return New_Assignment
                 (Ada_Node => N,
                  Name     => To_Why_Id (Lvalue),
                  Value    => Why_Expr);

            elsif Is_Static_Expression (Rexpr) then

               --  We generate an ignore statement, to obtain all the checks
               --  ??? Is this necessary? after all, we would get a compiler
               --  warning anyway

               return New_Ignore (Prog => Why_Expr);

            else
               declare
                  Tmp_Var : constant W_Identifier_Id :=
                    New_Identifier (Name => L_Name & "__assume",
                                    Typ  => EW_Abstract (Etype (Lvalue)));
                  Eq      : constant W_Pred_Id :=
                              New_Relation
                                (Op      => EW_Eq,
                                 Op_Type => Get_EW_Type (Lvalue),
                                 Left    => +Tmp_Var,
                                 Right   => +L_Id);
               begin
                  return
                    +New_Typed_Binding
                      (Ada_Node => N,
                       Domain   => EW_Prog,
                       Name     => Tmp_Var,
                       Def      => +Why_Expr,
                       Context  =>
                         +New_Assume_Statement
                           (Ada_Node => N,
                            Post     => Eq));
               end;
            end if;
         end;
      else
         return New_Void (N);
      end if;
   end Assignment_Of_Obj_Decl;

   ------------------------------
   -- Assume_Of_Scalar_Subtype --
   ------------------------------

   function Assume_Of_Scalar_Subtype
     (Params   : Transformation_Params;
      N        : Entity_Id;
      Base     : Entity_Id;
      Do_Check : Boolean) return W_Prog_Id
   is
   begin
      --  If the range is not static, we need to generate a check that
      --  the subtype declaration is valid; otherwise, the frontend has
      --  done it for us already

      if Is_Static_Range (Get_Range (N)) then
         return New_Void;
      else
         declare
            Rng              : constant Node_Id := Get_Range (N);
            Why_Base         : constant W_Type_Id := Base_Why_Type (N);
            Why_Base_EW      : constant EW_Type := Get_EW_Type (N);
            Low_Expr         : constant W_Term_Id :=
              +Transform_Expr (Low_Bound (Rng), Why_Base, EW_Term, Params);
            High_Expr        : constant W_Term_Id :=
              +Transform_Expr (High_Bound (Rng), Why_Base, EW_Term, Params);
            First_Term       : constant W_Term_Id :=
              +New_Attribute_Expr (N, Attribute_First);
            Last_Term        : constant W_Term_Id :=
              +New_Attribute_Expr (N, Attribute_Last);
            Rel_First        : constant W_Pred_Id :=
              New_Relation
                (Op_Type  => EW_Bool,
                 Left     => +Low_Expr,
                 Right    => +First_Term,
                 Op       => EW_Eq);
            Rel_Last         : constant W_Pred_Id :=
              New_Relation
                (Op_Type  => EW_Bool,
                 Left     => +High_Expr,
                 Right    => +Last_Term,
                 Op       => EW_Eq);
            First_In_Range   : constant W_Pred_Id :=
              New_Relation
                (Op_Type  => Why_Base_EW,
                 Left     => +Low_Expr,
                 Right    => +New_Attribute_Expr (Base, Attribute_First),
                 Op       => EW_Ge);
            Last_In_Range    : constant W_Pred_Id :=
              New_Relation
                (Op_Type  => Why_Base_EW,
                 Left     => +High_Expr,
                 Right    => +New_Attribute_Expr (Base, Attribute_Last),
                 Op       => EW_Le);
            First_Le_Last    : constant W_Pred_Id :=
              New_Relation
                (Op_Type  => Why_Base_EW,
                 Left     => +Low_Expr,
                 Right    => +High_Expr,
                 Op       => EW_Le);
            Precond          : constant W_Pred_Id :=
              +New_Connection
              (Op     => EW_Imply,
               Left   => +First_Le_Last,
               Right  =>
                 +New_And_Expr
                 (Domain => EW_Pred,
                  Left   => +First_In_Range,
                  Right => +Last_In_Range));
            Postcond        : constant W_Pred_Id :=
              +New_And_Expr (Domain => EW_Pred,
                             Left   => +Rel_First,
                             Right  => +Rel_Last);
            Assuming : W_Prog_Id;

         begin
            --  If the scalar subtype is modeled as "int" or "real", assign the
            --  variables corresponding to its bounds instead of assuming the
            --  values of constants corresponding to its bounds.

            if Type_Is_Modeled_As_Int_Or_Real (N) then
               declare
                  Low_Var : constant W_Expr_Id :=
                    +Get_Right
                      (W_Deref_Id (New_Attribute_Expr (N, Attribute_First)));
                  High_Var : constant W_Expr_Id :=
                    +Get_Right
                      (W_Deref_Id (New_Attribute_Expr (N, Attribute_Last)));
                  Set_Bounds : constant W_Prog_Id :=
                    Sequence (New_Assignment (Name => +Low_Var,
                                              Value => +Low_Expr),
                              New_Assignment (Name => +High_Var,
                                              Value => +High_Expr));
               begin
                  if Do_Check then
                     Assuming := New_Assume_Statement (Ada_Node => N,
                                                       Pre      => Precond,
                                                       Post     => True_Pred);
                     return
                       Sequence (Set_Bounds,
                                 +New_VC_Expr (Ada_Node => N,
                                               Domain   => EW_Prog,
                                               Reason   => VC_Range_Check,
                                               Expr     => +Assuming));
                  else
                     return Set_Bounds;
                  end if;
               end;

            --  Scalar subtype is modeled as abstract type, with constants for
            --  the bounds. Generate assumptions that relate these constants to
            --  their value.

            else
               if Do_Check then
                  Assuming := New_Assume_Statement (Ada_Node => N,
                                                    Pre      => Precond,
                                                    Post     => Postcond);
                  return +New_VC_Expr (Ada_Node => N,
                                       Domain   => EW_Prog,
                                       Reason   => VC_Range_Check,
                                       Expr     => +Assuming);

               else
                  Assuming :=
                    New_Assume_Statement
                      (Ada_Node => N,
                       Post     => +New_And_Expr (Domain => EW_Pred,
                                                  Left   => +Precond,
                                                  Right  => +Postcond));
                  return Assuming;
               end if;
            end if;
         end;
      end if;
   end Assume_Of_Scalar_Subtype;

   ----------------------------------
   -- Assume_Of_Subtype_Indication --
   ----------------------------------

   function Assume_Of_Subtype_Indication
     (Params   : Transformation_Params;
      N        : Node_Id;
      Sub_Type : Entity_Id;
      Do_Check : Boolean) return W_Prog_Id is
   begin
      if Is_Scalar_Type (Sub_Type) then
         return Assume_Of_Scalar_Subtype (Params   => Params,
                                          N        => Sub_Type,
                                          Base     => Etype (Subtype_Mark (N)),
                                          Do_Check => Do_Check);
      else
         return New_Void;
      end if;
   end Assume_Of_Subtype_Indication;

   -------------------------------
   -- Bind_From_Mapping_In_Expr --
   -------------------------------

   function Bind_From_Mapping_In_Expr
     (Params                 : Transformation_Params;
      Map                    : Ada_To_Why_Ident.Map;
      Expr                   : W_Prog_Id;
      Guard_Map              : Ada_To_Why_Ident.Map :=
        Ada_To_Why_Ident.Empty_Map;
      Others_Guard_Ident     : W_Identifier_Id := Why_Empty;
      Do_Runtime_Error_Check : Boolean := True;
      Bind_Value_Of_Old      : Boolean := False) return W_Prog_Id
   is
      function Get_Corresponding_Guard (N : Node_Id) return Node_Id;
      --  If N is inside the consequence expression of a contract case, returns
      --  the corresponding guard expression. Otherwise, returns Empty;

      -----------------------------
      -- Get_Corresponding_Guard --
      -----------------------------

      function Get_Corresponding_Guard (N : Node_Id) return Node_Id is
         P         : Node_Id;
         All_Cases : Node_Id;

      begin
         --  Retrieve the enclosing pragma, which may be either a postcondition
         --  or a contract_cases pragma.

         P := Parent (N);
         while Nkind (P) /= N_Pragma loop
            P := Parent (P);
         end loop;

         --  Return Empty for a postcondition pragma

         if Is_Pragma_Check (P, Name_Post)
              or else
            Is_Pragma_Check (P, Name_Postcondition)
              or else
            Is_Pragma (P, Pragma_Post)
              or else
            Is_Pragma (P, Pragma_Postcondition)
              or else
            Is_Pragma (P, Pragma_Refined_Post)
         then
            return Empty;
         end if;

         pragma Assert (Is_Pragma (P, Pragma_Contract_Cases));

         --  Retrieve the enclosing contract case component_association

         All_Cases :=
           Get_Pragma_Arg (First (Pragma_Argument_Associations (P)));

         P := Parent (N);
         while Parent (P) /= All_Cases loop
            P := Parent (P);
         end loop;

         pragma Assert (Nkind (P) = N_Component_Association);

         --  Return the guard of the enclosing contract case

         return First (Choices (P));
      end Get_Corresponding_Guard;

      Result : W_Prog_Id := Expr;

   --  Start of Bind_From_Mapping_In_Expr

   begin
      for C in Map.Iterate loop
         declare
            N     : constant Node_Id := Ada_To_Why_Ident.Key (C);
            Name  : constant W_Identifier_Id := Ada_To_Why_Ident.Element (C);
            Guard : constant Node_Id :=
              (if Bind_Value_Of_Old then
                  Get_Corresponding_Guard (N)
               else Empty);

            --  Generate a program expression to check absence of run-time
            --  errors. When checking for X in X'Old inside a contract case
            --  (which corresponds to Guard being non Empty), do this checking
            --  only under a condition that the corresponding case is enabled.

            RE_Prog : constant W_Prog_Id :=
              (if Do_Runtime_Error_Check then
                (if Present (Guard) then
                  New_Conditional
                    (Condition =>
                       +(if Nkind (Guard) = N_Others_Choice then
                           Others_Guard_Ident
                         else
                           Guard_Map.Element (Guard)),
                     Then_Part => +New_Ignore
                       (Prog => +Transform_Expr (N, EW_Prog, Params)))
                 else
                   New_Ignore (Prog => +Transform_Expr (N, EW_Prog, Params)))
               else
                 New_Void);

            --  Generate a term definition for the value of the object at
            --  subprogram entry, and link with rest of code. This
            --  definition does not involve lazy boolean operators, so it
            --  does not lead to more paths being generated in the naive WP,
            --  contrary to what we would get if directly defining the value
            --  of the object as a program. This is particularly useful for
            --  guards of Contract_Cases.

            Let_Prog : constant W_Prog_Id :=
              +New_Typed_Binding
                (Name   => Name,
                 Domain => EW_Prog,
                 Def    =>
                   +New_Simpl_Any_Prog
                   (T    => Get_Typ (Name),
                    Pred =>
                      +W_Expr_Id'(New_Relation
                      (Domain   => EW_Pred,
                       Op_Type  => EW_Bool,
                       Left     => +New_Result_Ident (EW_Abstract (Etype (N))),
                       Op       => EW_Eq,
                       Right    =>
                         +Transform_Expr (N, EW_Term, Params)))),
                 Context => +Result);
         begin
            Result := Sequence (RE_Prog, Let_Prog);
         end;
      end loop;

      return Result;
   end Bind_From_Mapping_In_Expr;

   ---------------------------
   -- Case_Expr_Of_Ada_Node --
   ---------------------------

   function Case_Expr_Of_Ada_Node
     (N             : Node_Id;
      Expected_Type : W_Type_OId := Why_Empty;
      Domain        : EW_Domain;
      Params        : Transformation_Params) return W_Expr_Id
   is
      --  For a given case expression
      --
      --    case X is
      --       when Case_1 => S1
      --       ...
      --       when Case_n => Sn
      --       when others => S
      --    end case;
      --
      --  We generate a single if expression, with a list of elsif cases, to
      --  avoid the generation of deep Why3 expressions, which may lead to
      --  stack overflow when traversing recursively the expression:
      --
      --    if X = Case_1 then S1
      --    elsif ...
      --    elsif X = Case_N then Sn
      --    else S

      function Branch_Expr (N : Node_Id) return W_Expr_Id;
      --  Return the expression that corresponds to a branch; decide which
      --  function to call depending on the type of the branch.

      -----------------
      -- Branch_Expr --
      -----------------

      function Branch_Expr (N : Node_Id) return W_Expr_Id is
         T : W_Expr_Id;

      begin
         case Nkind (N) is
            when N_Case_Expression_Alternative =>
               Ada_Ent_To_Why.Push_Scope (Symbol_Table);
               if Present (Actions (N)) then
                  Transform_Actions_Preparation (Actions (N));
               end if;

               if Expected_Type = Why_Empty then
                  T := Transform_Expr (Expression (N),
                                       Domain,
                                       Params);
               else
                  T := Transform_Expr (Expression (N),
                                       Expected_Type,
                                       Domain,
                                       Params);
               end if;

               if Present (Actions (N)) then
                  T := Transform_Actions (Actions (N),
                                          T,
                                          Domain,
                                          Params);
               end if;
               Ada_Ent_To_Why.Pop_Scope (Symbol_Table);

               return T;

            when N_Case_Statement_Alternative =>
               --  ??? Maybe we should merge the code for statements?
               return +Transform_Statements_And_Declarations (Statements (N));

            when others =>
               raise Unexpected_Node;

         end  case;
      end Branch_Expr;

      Match_Domain : constant EW_Domain :=
         (if Domain = EW_Pred then EW_Term else Domain);
      Cond_Domain  : constant EW_Domain :=
         (if Domain = EW_Term then EW_Pred else Domain);

      Cases        : constant List_Id := Alternatives (N);
      First_Case   : constant Node_Id := First (Cases);
      Last_Case    : constant Node_Id := Last (Cases);
      Expr         : constant Node_Id := Expression (N);
      Cur_Case     : Node_Id;
      Matched_Expr : constant W_Expr_Id :=
                       Transform_Expr (Expr,
                                       EW_Int_Type,
                                       Match_Domain,
                                       Params);
      Then_Expr    : constant W_Expr_Id := Branch_Expr (First_Case);
      Elsif_Parts  : W_Expr_Array (1 .. Integer (List_Length (Cases)) - 2);

      --  beginning of processing for Case_Expr_Of_Ada_Node
   begin
      if List_Length (Cases) = 1 then
         return Then_Expr;

      else
         Cur_Case := Next (First_Case);
         for Offset in 1 .. List_Length (Cases) - 2 loop
            Elsif_Parts (Integer (Offset)) :=
              New_Elsif
                (Domain    => Domain,
                 Condition =>
                   Transform_Discrete_Choices
                     (Choices      => Discrete_Choices (Cur_Case),
                      Choice_Type  => Etype (Expr),
                      Matched_Expr => Matched_Expr,
                      Cond_Domain  => Cond_Domain,
                      Params       => Params),
                 Then_Part => Branch_Expr (Cur_Case));
            Next (Cur_Case);
         end loop;

         return New_Conditional
           (Domain      => Domain,
            Condition   =>
              Transform_Discrete_Choices
                (Choices      => Discrete_Choices (First_Case),
                 Choice_Type  => Etype (Expr),
                 Matched_Expr => Matched_Expr,
                 Cond_Domain  => Cond_Domain,
                 Params       => Params),
            Then_Part   => Then_Expr,
            Elsif_Parts => Elsif_Parts,
            Else_Part   => Branch_Expr (Last_Case),
            Typ         => Get_Type (Then_Expr));
      end if;
   end Case_Expr_Of_Ada_Node;

   -----------------------
   -- Compute_Call_Args --
   -----------------------

   function Compute_Call_Args
     (Call        : Node_Id;
      Domain      : EW_Domain;
      Nb_Of_Refs  : out Natural;
      Params      : Transformation_Params) return W_Expr_Array
   is
      Subp   : constant Entity_Id := Entity (Name (Call));
      Assocs : constant List_Id := Parameter_Associations (Call);
      Len    : Nat;

      Read_Ids    : Flow_Types.Flow_Id_Sets.Set;
      Write_Ids   : Flow_Types.Flow_Id_Sets.Set;
      Read_Names  : Name_Set.Set;

   begin
      --  Collect global variables potentially read

      Flow.Utility.Get_Proof_Globals (Subprogram => Subp,
                                      Reads      => Read_Ids,
                                      Writes     => Write_Ids);
      Read_Names := Flow_Types.To_Name_Set (Read_Ids);

      Nb_Of_Refs := 0;
      Len := List_Length (Assocs);

      if Domain = EW_Term then
         Len := Len + Int (Read_Names.Length);
      end if;

      if Len = 0 then
         return (1 => New_Void (Call));
      end if;

      declare
         Why_Args : W_Expr_Array (1 .. Integer (Len));
         Cnt      : Positive := 1;

         procedure Compute_Arg (Formal, Actual : Node_Id);
         --  Compute a Why expression for each parameter

         -----------------
         -- Compute_Arg --
         -----------------

         procedure Compute_Arg (Formal, Actual : Node_Id) is
         begin
            if Needs_Temporary_Ref (Actual, Formal) then

               --  We should never use the Formal for the Ada_Node,
               --  because there is no real dependency here; We only
               --  use the Formal to get a sensible name.

               Why_Args (Cnt) :=
                 +New_Identifier (Ada_Node => Empty,
                                  Name     => Full_Name (Formal));
               Nb_Of_Refs := Nb_Of_Refs + 1;
            else
               case Ekind (Formal) is
                  when E_In_Out_Parameter | E_Out_Parameter =>

                     --  Parameters that are "out" are refs;
                     --  if the actual is a simple identifier and no conversion
                     --  is needed, it can be translated "as is".

                     Why_Args (Cnt) :=
                       +New_Identifier (Ada_Node => Actual,
                                        Name     => Full_Name (Actual));

                     --  If a conversion or a component indexing is needed,
                     --  it can only be done for a value. That is to say,
                     --  something of this sort should be generated:
                     --
                     --  let formal = ref to_formal (!actual) in
                     --   (subprogram_call (formal); actual := !formal)
                     --
                     --  The generation of the context is left to the caller;
                     --  this function only signals the existence of such
                     --  parameters by incrementing Nb_Of_Refs.

                  when others =>

                     --  When the formal is an "in" scalar, we actually use
                     --  "int" as a type.

                     Why_Args (Cnt) :=
                       Transform_Expr (Actual,
                                       (if Use_Why_Base_Type (Formal) then
                                           Base_Why_Type
                                          (Unique_Entity (Etype (Formal)))
                                        else
                                           Type_Of_Node (Formal)),
                                       Domain,
                                       Params);
               end case;
            end if;
            Cnt := Cnt + 1;
         end Compute_Arg;

         procedure Iterate_Call is new
           Iterate_Call_Arguments (Compute_Arg);
      begin
         Iterate_Call (Call);

         if Domain = EW_Term then
            for Elt of Read_Names loop
               declare
                  C : constant Ada_Ent_To_Why.Cursor :=
                        Ada_Ent_To_Why.Find (Symbol_Table, Elt);
                  T : W_Expr_Id;
               begin

                  --  If the effect parameter is found in the map, use the name
                  --  stored.

                  if Ada_Ent_To_Why.Has_Element (C) then
                     T := +Ada_Ent_To_Why.Element (C).Main.B_Name;
                  else
                     T := +To_Why_Id (Elt.all, Local => False);
                  end if;

                  if Params.Ref_Allowed then
                     Why_Args (Cnt) := New_Deref (Right => +T);
                  else
                     Why_Args (Cnt) := T;
                  end if;
               end;
               Cnt := Cnt + 1;
            end loop;

            --  We also need to add inclusions to allow the usage of those read
            --  variables

            Add_Effect_Imports (Params.Theory, Read_Names);
         end if;

         return Why_Args;
      end;
   end Compute_Call_Args;

   ------------------------------
   -- Discrete_Choice_Is_Range --
   ------------------------------

   function Discrete_Choice_Is_Range (Choice : Node_Id) return Boolean is
      Is_Range : Boolean;
   begin
      case Nkind (Choice) is
         when N_Subtype_Indication | N_Range =>
            Is_Range := True;
         when N_Identifier | N_Expanded_Name =>
            if Ekind (Entity (Choice)) in Type_Kind then
               Is_Range := True;
            else
               Is_Range := False;
            end if;
         when N_Others_Choice =>
            Is_Range := True;
         when others =>
            Is_Range := False;
      end case;
      return Is_Range;
   end Discrete_Choice_Is_Range;

   -----------------------------
   -- Expected_Type_Of_Prefix --
   -----------------------------

   function Expected_Type_Of_Prefix (N : Node_Id) return W_Type_Id is
   begin
      case Nkind (N) is
         when N_Identifier | N_Expanded_Name =>
            return
              Get_Typ (Ada_Ent_To_Why.Element
                       (Symbol_Table, Entity (N)).Main.B_Name);

         when N_Slice =>
            return Type_Of_Node (Unique_Entity (Etype (Prefix (N))));

         when N_Indexed_Component =>
            return Type_Of_Node
              (Component_Type (Unique_Entity (Etype (Prefix (N)))));

         when N_Selected_Component =>
            return Type_Of_Node (Selector_Name (N));

         when others =>
            Ada.Text_IO.Put_Line ("[Expected_Type] kind ="
                                  & Node_Kind'Image (Nkind (N)));
            raise Not_Implemented;
      end case;
   end Expected_Type_Of_Prefix;

   ---------------------------------------------
   -- Get_Container_In_Iterator_Specification --
   ---------------------------------------------

   function Get_Container_In_Iterator_Specification
     (N : Node_Id) return Node_Id
   is
      Iter : constant Node_Id := Name (N);
   begin
      return (Iter);
   end Get_Container_In_Iterator_Specification;

   ---------------------------------------
   -- Get_Iterable_Has_Element_Function --
   ---------------------------------------

   function Get_Iterable_Has_Element_Function
     (E : Entity_Id) return Entity_Id
   is
      Iterable_Aspect : constant Node_Id := Get_Iterable_Aspect (E);
   begin
      pragma Assert (Present (Iterable_Aspect));

      declare
         Iterable_Component_Assoc : constant List_Id :=
           Component_Associations (Expression (Iterable_Aspect));
         Iterable_Field : Node_Id := First (Iterable_Component_Assoc);

      begin

         while Present (Iterable_Field) loop
            declare
               Choice : Node_Id := First (Choices (Iterable_Field));
            begin

               while Present (Choice) loop
                  if Chars (Choice) = Name_Has_Element then
                     return Entity (Expression (Iterable_Field));
                  end if;
                  Next (Choice);
               end loop;
            end;

            Next (Iterable_Field);
         end loop;

         return Iterable_Field;
      end;
   end Get_Iterable_Has_Element_Function;

   -------------------------------------
   -- Get_Pure_Logic_Term_If_Possible --
   -------------------------------------

   function Get_Pure_Logic_Term_If_Possible
     (File          : Why_Section;
      Expr          : Node_Id;
      Expected_Type : W_Type_Id) return W_Term_Id
   is
      Params : constant Transformation_Params :=
        (Theory      => File.Cur_Theory,
         File        => File.File,
         Phase       => Generate_Logic,
         Gen_Image   => False,
         Ref_Allowed => True);
      Result : constant W_Term_Id :=
        +Transform_Expr (Expr, Expected_Type, EW_Term, Params);
   begin
      if Has_Dereference_Or_Any (Result) then
         return Why_Empty;
      else
         return Result;
      end if;
   end Get_Pure_Logic_Term_If_Possible;

   ----------------------
   -- Has_Element_Expr --
   ----------------------

   function Has_Element_Expr
     (Cont   : Node_Id;
      Cursor : W_Expr_Id;
      Domain : EW_Domain;
      Params : Transformation_Params) return W_Expr_Id
   is
      Subdomain       : constant EW_Domain :=
                    (if Domain = EW_Pred then EW_Term else Domain);
      Subp            : constant Entity_Id :=
        Get_Iterable_Has_Element_Function (Etype (Cont));
      Name            : constant W_Identifier_Id :=
        To_Why_Id (Subp, Domain, Local => False);
      Call            : constant W_Expr_Id :=
                          New_Call
                            (Domain   => Domain,
                             Name     => Name,
                             Args     =>
                               (1 => Transform_Expr (Cont, Subdomain, Params),
                                2 => Cursor));
   begin
      if Domain = EW_Pred then
         return New_Relation (Domain  => EW_Pred,
                              Op_Type => EW_Bool,
                              Left    => +Call,
                              Op      => EW_Eq,
                              Right   => +True_Term);
      else
         return Call;
      end if;
   end Has_Element_Expr;

   ---------------------------
   -- Insert_Overflow_Check --
   ---------------------------

   function Insert_Overflow_Check
     (Ada_Node : Node_Id;
      T        : W_Expr_Id;
      In_Type  : Entity_Id) return W_Expr_Id
   is
      Base : constant Entity_Id := Base_Type (In_Type);

   begin
      return New_VC_Call (Domain   => EW_Prog,
                          Ada_Node => Ada_Node,
                          Name     => Prefix (M        => E_Module (Base),
                                              W        => WNE_Range_Check_Fun,
                                              Ada_Node => Base),
                          Progs    => (1 => +T),
                          Reason   => VC_Overflow_Check,
                          Typ      => Get_Type (T));
   end Insert_Overflow_Check;

   ------------------------
   -- Insert_Ref_Context --
   ------------------------

   function Insert_Ref_Context
     (Params     : Transformation_Params;
      Ada_Call   : Node_Id;
      Why_Call   : W_Prog_Id;
      Nb_Of_Refs : Positive) return W_Prog_Id
   is
      --  This goes recursively through the out/"in out" parameters
      --  to be converted; and collects, for each of them:
      --
      --  * the name of the corresponding tmp variable;
      --  * the expression of the conversion from the actual to the tmp;
      --  * a statement sequence for the conversions back to the actual.
      --
      --  The first two are set together after that. It cannot be done
      --  during the recursive traversal, as we are building its
      --  children during the traversal and that only root nodes can have
      --  their children modified.

      Ref_Context : W_Prog_Id;
      Index       : Positive := 1;
      Tmp_Vars    : W_Identifier_Array (1 .. Nb_Of_Refs);
      Fetch       : W_Prog_Array (1 .. Nb_Of_Refs);
      Store       : constant W_Statement_Sequence_Unchecked_Id :=
                      New_Unchecked_Statement_Sequence;

      procedure Process_Arg (Formal, Actual : Node_Id);

      -----------------
      -- Process_Arg --
      -----------------

      procedure Process_Arg (Formal, Actual : Node_Id) is
      begin
         if Needs_Temporary_Ref (Actual, Formal) then
            declare
               --  Types:

               Formal_T      : constant W_Type_Id :=
                                 Type_Of_Node (Formal);
               Actual_T      : constant W_Type_Id :=
                                 Type_Of_Node (Actual);

               --  Variables:

               --  We should never use the Formal for the Ada_Node,
               --  because there is no real dependency here; We only
               --  use the Formal to get a sensible name.

               Tmp_Var       : constant W_Identifier_Id :=
                 New_Identifier (Ada_Node => Empty,
                                 Name     => Full_Name (Formal),
                                 Typ      => Formal_T);
               Tmp_Var_Deref : constant W_Prog_Id :=
                 New_Deref (Right => Tmp_Var,
                            Typ   => Formal_T);

               --  1/ Before the call (saving into a temporary variable):
               ----------------------------------------------------------

               --  On fetch, checks are only needed when the formal is a scalar
               --  IN or IN OUT, and potentially always needed for composite
               --  parameters.

               Need_Check_On_Fetch : constant Boolean :=
                 (if Ekind (MUT (Etype (Formal)))
                       in Scalar_Kind
                  then
                    Ekind (Formal) /= E_Out_Parameter
                  else
                    True);

               --  Generate an expression of the form:
               --
               --    to_formal_type (from_actual_type (!actual))
               --
               --  ... with the appropriate checks if needed.

               Prefetch_Actual : constant W_Prog_Id :=
                 +Transform_Expr (Actual,
                                  EW_Prog,
                                  Params);

               Fetch_Actual  : constant W_Prog_Id :=
                 (if Need_Check_On_Fetch then
                   +Insert_Checked_Conversion (Ada_Node => Actual,
                                               Ada_Type => Etype (Actual),
                                               Domain   => EW_Prog,
                                               Expr     => +Prefetch_Actual,
                                               To       => Formal_T)
                  else
                   +Insert_Simple_Conversion (Ada_Node => Actual,
                                              Domain   => EW_Prog,
                                              Expr     => +Prefetch_Actual,
                                              To       => Formal_T));

               --  2/ After the call (storing the result):
               -------------------------------------------

               --  On store, checks are only needed when the formal is a scalar
               --  OUT or IN OUT, and never needed for composite parameters.

               Need_Check_On_Store : constant Boolean :=
                 (if Ekind (MUT (Etype (Formal)))
                       in Scalar_Kind
                  then
                    Ekind (Formal) /= E_In_Parameter
                  else
                    False);

               --  Generate an expression of the form:
               --
               --    to_actual_type_ (from_formal_type (!tmp_var))
               --
               --  ... with the appropriate checks if needed.

               Arg_Value     : constant W_Prog_Id :=
                 (if Need_Check_On_Store then
                   +Insert_Checked_Conversion (Ada_Node => Actual,
                                               Ada_Type => Etype (Actual),
                                               Domain   => EW_Prog,
                                               Expr     => +Tmp_Var_Deref,
                                               To       => Actual_T)
                  else
                   +Insert_Simple_Conversion (Ada_Node => Actual,
                                              Domain   => EW_Prog,
                                              Expr     => +Tmp_Var_Deref,
                                              To       => Actual_T));

               --  ...then store it into the actual:

               Store_Value   : constant W_Prog_Id :=
                                 New_Assignment
                                   (Ada_Node => Actual,
                                    Lvalue   => Actual,
                                    Expr     => Arg_Value);
            begin
               Statement_Sequence_Append_To_Statements (Store, Store_Value);
               Tmp_Vars (Index) := Tmp_Var;
               Fetch (Index) := Fetch_Actual;
               Index := Index + 1;
            end;
         end if;
      end Process_Arg;

      procedure Iterate_Call is new
        Iterate_Call_Arguments (Process_Arg);

   --  Start of processing for Insert_Ref_Context

   begin
      Statement_Sequence_Append_To_Statements (Store, Why_Call);
      Iterate_Call (Ada_Call);

      --  Set the pieces together

      Ref_Context := +Store;
      for J in Fetch'Range loop
         Ref_Context :=
           New_Binding_Ref
             (Name    => Tmp_Vars (J),
              Def     => Fetch (J),
              Context => Ref_Context);
      end loop;

      return Ref_Context;
   end Insert_Ref_Context;

   --------------------
   -- Is_Pretty_Node --
   --------------------

   function Is_Pretty_Node (N : Node_Id) return Boolean is
   begin
      case Nkind (N) is
         when N_Quantified_Expression | N_And_Then |
              N_Op_And | N_If_Expression
            => return False;
         when others => return True;
      end case;
   end Is_Pretty_Node;

   -------------------------
   -- Name_For_Loop_Entry --
   -------------------------

   function Name_For_Loop_Entry
     (Expr    : Node_Id;
      Loop_Id : Node_Id) return W_Identifier_Id
   is
      Result : W_Identifier_Id;

      procedure Get_Name
        (Loop_Id  : Node_Id;
         Loop_Map : in out Ada_To_Why_Ident.Map);
      --  Update the mapping Loop_Map with an entry for Expr if not already
      --  present, and store in Result the corresponding identifier.

      --------------
      -- Get_Name --
      --------------

      procedure Get_Name
        (Loop_Id  : Node_Id;
         Loop_Map : in out Ada_To_Why_Ident.Map)
      is
         Typ : W_Type_Id;
         Nd  : Node_Id := Empty;
      begin
         pragma Unreferenced (Loop_Id);

         if not Loop_Map.Contains (Expr) then

            if Nkind (Expr) in N_Identifier | N_Expanded_Name then
               Typ := Why_Type_Of_Entity (Entity (Expr));
               Nd  := Entity (Expr);
            else
               Typ := EW_Abstract (Etype (Expr));
            end if;
            Loop_Map.Include
              (Expr,
               New_Temp_Identifier
                 (Typ      => Typ,
                  Ada_Node => Nd));
         end if;

         Result := Loop_Map.Element (Expr);
      end Get_Name;

   --  Start of Name_For_Loop_Entry

   begin
      if not Loop_Entry_Map.Contains (Loop_Id) then
         declare
            Empty_Map : Ada_To_Why_Ident.Map;
         begin
            Loop_Entry_Map.Include (Loop_Id, Empty_Map);
         end;
      end if;

      Loop_Entry_Map.Update_Element
        (Position => Loop_Entry_Map.Find (Loop_Id),
         Process  => Get_Name'Access);

      return Result;
   end Name_For_Loop_Entry;

   ------------------
   -- Name_For_Old --
   ------------------

   function Name_For_Old (N : Node_Id) return W_Identifier_Id is
      Typ : W_Type_Id;
      Nd  : Node_Id := Empty;
   begin
      if not Old_Map.Contains (N) then
         if Nkind (N) in N_Identifier | N_Expanded_Name then
            Typ := Why_Type_Of_Entity (Entity (N));
            Nd := Entity (N);
         else
            Typ := EW_Abstract (Etype (N));
         end if;
         Old_Map.Include
           (N,
            New_Temp_Identifier
              (Typ      => Typ,
               Ada_Node => Nd));
      end if;

      return Old_Map.Element (N);
   end Name_For_Old;

   ---------------------
   -- Name_For_Result --
   ---------------------

   function Name_For_Result return W_Identifier_Id is
   begin
      pragma Assert (Result_Name /= Why_Empty);
      return Result_Name;
   end Name_For_Result;

   -------------------------
   -- Needs_Temporary_Ref --
   -------------------------

   function Needs_Temporary_Ref
     (Actual : Node_Id;
      Formal : Node_Id) return Boolean is
   begin
      --  Temporary refs are needed for out or in out parameters that
      --  need a conversion or who are not an identifier.
      case Ekind (Formal) is
         when E_In_Out_Parameter | E_Out_Parameter =>
            return not Eq (Etype (Actual), Etype (Formal))
              or else not (Nkind (Actual) in N_Entity);
         when E_In_Parameter =>
            return Has_Async_Writers (Direct_Mapping_Id (Formal));
         when others =>
            return False;
      end case;
   end Needs_Temporary_Ref;

   --------------------
   -- New_Assignment --
   --------------------

   function New_Assignment
     (Ada_Node : Node_Id := Empty;
      Lvalue   : Node_Id;
      Expr     : W_Prog_Id) return W_Prog_Id
   is
      --  Here, we deal with assignment statements. In SPARK, the general form
      --  of an assignment is
      --
      --    Lvalue := Expr;
      --
      --  where Lvalue is a mix of array and record accesses. If we adopt the
      --  same notation for both, we obtain the general form
      --
      --    Prefix.Acc1.Acc2.(...).Accn := Expr;
      --
      --  where the Acc(i) are either array accesses using an index (or
      --  several indices in the multidimensional case) or record accesses
      --  using a field name.
      --
      --  Here, we generate Why code of the form
      --
      --    Prefix := Upd (Prefix, Acc1,
      --                   (Upd (Prefix.Acc1, Acc2,
      --                         Upd (..., Accn, Expr))));

      procedure Shift_Rvalue
        (N         : in out Node_Id;
         Expr      : in out W_Prog_Id);
      --  the input triple (N, Expr, Expr_Type) describes an assignment
      --      N := Expr
      --  where N is the Ada node for some Lvalue of the form
      --    Prefix.Acc1.(...).Acc[n-1].Accn := Expr;
      --  Expr_Type is the type in which the assignment takes place, ie. the
      --  type of Expr and of Accn.
      --  The *output* triple (N, Expr, Expr_Type) corresponds to the same
      --  assignment, but shifting the Accn to the right side and transforming
      --  it into an update. We obtain
      --    Prefix.Acc1.(...).Acc[n-1] :=
      --         Upd (Prefix.Acc1.(...).Acc[n-1], Accn, Expr)

      ------------------
      -- Shift_Rvalue --
      ------------------

      procedure Shift_Rvalue
        (N         : in out Node_Id;
         Expr      : in out W_Prog_Id) is
      begin
         case Nkind (N) is
            when N_Identifier | N_Expanded_Name =>
               null;

            when N_Type_Conversion =>
                  N := Expression (N);
                  Expr :=
                    +Insert_Simple_Conversion
                      (Domain => EW_Prog,
                       Expr   => +Expr,
                       To     => EW_Abstract (Etype (N)));

            when N_Selected_Component | N_Indexed_Component | N_Slice =>
               declare
                  Prefix_Type : constant W_Type_Id :=
                    Expected_Type_Of_Prefix (Prefix (N));
                  Prefix_Expr : constant W_Expr_Id :=
                    +Transform_Expr (Domain        => EW_Prog,
                                     Expr          => Prefix (N),
                                     Expected_Type => Prefix_Type,
                                     Params        => Body_Params);
               begin
                  Expr :=
                    +One_Level_Update (N,
                                       +Prefix_Expr,
                                       +Expr,
                                       EW_Prog,
                                       Params => Body_Params);
                  N := Prefix (N);
               end;

            when others =>
               Ada.Text_IO.Put_Line ("[Compute_Rvalue] kind ="
                                     & Node_Kind'Image (Nkind (N)));
               raise Not_Implemented;
         end case;
      end Shift_Rvalue;

      --  begin processing for Transform_Assignment_Statement

      Left_Side  : Node_Id := Lvalue;
      Right_Side : W_Prog_Id := Expr;
   begin
      while not (Nkind (Left_Side) in N_Identifier | N_Expanded_Name) loop
         Shift_Rvalue (Left_Side, Right_Side);
      end loop;
      return
        New_Assignment
          (Ada_Node => Ada_Node,
           Name     => To_Why_Id (Entity (Left_Side)),
           Value    => Right_Side);
   end New_Assignment;

   ----------------------
   -- One_Level_Access --
   ----------------------

   function One_Level_Access
     (N            : Node_Id;
      Expr         : W_Expr_Id;
      Domain       : EW_Domain;
      Params       : Transformation_Params) return W_Expr_Id is
   begin
      case Nkind (N) is
         when N_Selected_Component =>
            declare
               Sel_Ent : constant Entity_Id := Entity (Selector_Name (N));
               Id      : constant W_Identifier_Id := To_Why_Id (Sel_Ent);
               Rec_Ty  : constant Entity_Id :=
                 Unique_Entity (Etype (Prefix (N)));
            begin
               if Is_Access_To_External_Axioms_Discriminant (N) then
                  return
                    New_Call (Ada_Node => N,
                              Domain   => Domain,
                              Name     => Id,
                              Args     => (1 => Expr),
                              Typ      => Type_Of_Node (N));
               else
                  return
                    New_Ada_Record_Access
                      (Ada_Node => N,
                       Domain   => Domain,
                       Name     => Expr,
                       Ty       => Rec_Ty,
                       Field    => Sel_Ent);
               end if;
            end;

         when N_Indexed_Component =>

            --  ??? Save the index in a temporary variable

            declare
               Ar      : constant Node_Id := Prefix (N);
               Dim     : constant Pos := Number_Dimensions (Type_Of_Node (Ar));
               Indices : W_Expr_Array (1 .. Integer (Dim));
               Cursor  : Node_Id := First (Expressions (N));
               Count   : Positive := 1;
            begin
               while Present (Cursor) loop
                  Indices (Count) :=
                     Transform_Expr
                        (Cursor, EW_Int_Type, Domain, Params);
                  Count := Count + 1;
                  Next (Cursor);
               end loop;

               return
                  New_Array_Access
                   (Ada_Node  => N,
                    Domain    => Domain,
                    Ar        => Expr,
                    Index     => Indices);
            end;

         when others =>
            Ada.Text_IO.Put_Line ("[One_Level_Access] kind ="
                                  & Node_Kind'Image (Nkind (N)));
            raise Not_Implemented;
      end case;
   end One_Level_Access;

   ----------------------
   -- One_Level_Update --
   ----------------------

   function One_Level_Update
     (N           : Node_Id;
      Pref        : W_Expr_Id;
      Value       : W_Expr_Id;
      Domain      : EW_Domain;
      Params      : Transformation_Params) return W_Expr_Id is
   begin
      case Nkind (N) is
         when N_Selected_Component =>

            --  The code should never update the capacity of a container by
            --  assigning to it. This is ensured by making the formal container
            --  type a private type, but keep the assertion in case.

            pragma Assert (not Is_Access_To_External_Axioms_Discriminant (N));

            return New_Ada_Record_Update
              (Ada_Node => N,
               Domain   => Domain,
               Name     => Pref,
               Field    => Entity (Selector_Name (N)),
               Value    =>
                  Insert_Simple_Conversion
                 (Ada_Node => N,
                  Domain   => Domain,
                  Expr     => Value,
                  To       =>
                     EW_Abstract (Etype (Entity (Selector_Name (N))))));

         when N_Indexed_Component =>
            declare
               Dim     : constant Pos :=
                  Number_Dimensions (Type_Of_Node (Prefix (N)));
               Indices : W_Expr_Array (1 .. Integer (Dim));
               Cursor  : Node_Id := First (Expressions (N));
               Count   : Positive := 1;
            begin
               while Present (Cursor) loop
                  Indices (Count) :=
                     Transform_Expr
                        (Cursor, EW_Int_Type, EW_Prog, Params);
                  Count := Count + 1;
                  Next (Cursor);
               end loop;
               return
                  New_Array_Update (Ada_Node  => N,
                                    Ar        => Pref,
                                    Index     => Indices,
                                    Value     => Value,
                                    Domain    => Domain);
            end;

         when N_Slice =>
            declare
               Prefix_Name : constant W_Identifier_Id :=
                 New_Temp_Identifier (Typ => Get_Type (Pref));
               Value_Name  : constant W_Identifier_Id :=
                 New_Temp_Identifier (Typ => Get_Type (Value));
               Prefix_Expr : constant W_Expr_Id :=
                               +Transform_Expr
                                 (Prefix (N),
                                  Domain        => EW_Term,
                                  Expected_Type => Get_Type (Pref),
                                  Params        => Params);
               Dim     : constant Pos :=
                  Number_Dimensions (Type_Of_Node (Prefix (N)));
               Result_Id   : constant W_Identifier_Id :=
                 New_Result_Ident (Get_Type (Pref));
               Binders     : constant W_Identifier_Array :=
                 New_Temp_Identifiers (Positive (Dim), Typ => EW_Int_Type);
               Ada_Type    : constant Entity_Id :=
                 Get_Ada_Node (+Get_Type (Pref));
               Indexes     : constant W_Expr_Array := To_Exprs (Binders);
               Range_Pred  : constant W_Expr_Id :=
                               Transform_Discrete_Choice
                                 (Choice => Discrete_Range (N),
                                  Choice_Type =>
                                    Etype (First_Index (Ada_Type)),
                                  Expr   => Indexes (1),
                                  Domain => EW_Pred,
                                  Params => Params);
               In_Slice_Eq : constant W_Pred_Id :=
                               New_Element_Equality
                                 (Left_Arr   => +Result_Id,
                                  Right_Arr  => +Value_Name,
                                  Index      => Indexes);
               Unchanged   : constant W_Pred_Id :=
                               New_Element_Equality
                                 (Left_Arr   => +Result_Id,
                                  Right_Arr  => +Prefix_Name,
                                  Index      => Indexes);

               Def         : constant W_Pred_Id :=
                               New_Conditional
                                 (Condition => Range_Pred,
                                  Then_Part => +In_Slice_Eq,
                                  Else_Part => +Unchanged);
               Quantif     : constant W_Expr_Id :=
                               New_Universal_Quantif
                                 (Variables => Binders,
                                  Var_Type  => +EW_Int_Type,
                                  Labels      => Name_Id_Sets.Empty_Set,
                                  Pred      => Def);
            begin
               return
                 New_Typed_Binding
                   (Domain => EW_Prog,
                    Name   => Prefix_Name,
                    Def    => Prefix_Expr,
                    Context =>
                      New_Typed_Binding
                        (Domain  => EW_Prog,
                         Name    => Value_Name,
                         Def     => +Value,
                         Context => +New_Simpl_Any_Prog
                           (T => Get_Type (Pref),
                            Pred => +Quantif)));
            end;

         when others =>
            Ada.Text_IO.Put_Line ("[One_Level_Update] kind ="
                                  & Node_Kind'Image (Nkind (N)));
            raise Not_Implemented;
      end case;

   end One_Level_Update;

   ----------------
   -- Range_Expr --
   ----------------

   function Range_Expr
     (N           : Node_Id;
      T           : W_Expr_Id;
      Domain      : EW_Domain;
      Params      : Transformation_Params;
      T_Type      : W_Type_OId := Why_Empty) return W_Expr_Id
   is
      Subdomain  : constant EW_Domain :=
                     (if Domain = EW_Pred then EW_Term else Domain);
      Range_Node : constant Node_Id := Get_Range (N);
      Low        : constant Node_Id := Low_Bound (Range_Node);
      High       : constant Node_Id := High_Bound (Range_Node);
      Base_Type  : W_Type_Id := Base_Why_Type (Low, High);

      R : W_Expr_Id;

   begin
      if T_Type /= Why_Empty then
         Base_Type := Base_Why_Type (T_Type, Base_Type);
      end if;

      --  Another special case for booleans: The above base type computations
      --  return "bool" for Standard_Boolean, but in fact for a boolean range
      --  we still want to have "int" here.

      if Base_Type = EW_Bool_Type then
         Base_Type := EW_Int_Type;
      end if;

      R := New_Range_Expr
          (Domain    => Domain,
           Low       => +Transform_Expr (Low, Base_Type, Subdomain, Params),
           High      => +Transform_Expr (High, Base_Type, Subdomain, Params),
           Expr      => T);

      --  In programs, we generate a check that the range_constraint of a
      --  subtype_indication is compatible with the given subtype.

      if Domain = EW_Prog
        and then Nkind (N) = N_Subtype_Indication
      then
         R := +Sequence
                (Assume_Of_Subtype_Indication (Params   => Params,
                                               N        => N,
                                               Sub_Type => Etype (N),
                                               Do_Check => True),
                 +R);
      end if;

      return R;
   end Range_Expr;

   -----------------------
   -- Reset_Map_For_Old --
   -----------------------

   procedure Reset_Map_For_Old is
   begin
      Old_Map.Clear;
   end Reset_Map_For_Old;

   -----------------------
   -- Transform_Actions --
   -----------------------

   function Transform_Actions
     (Actions : List_Id;
      Expr    : W_Expr_Id;
      Domain  : EW_Domain;
      Params  : Transformation_Params) return W_Expr_Id
   is
      T : W_Expr_Id;
      N : Node_Id;

      Subdomain : constant EW_Domain :=
        (if Domain = EW_Pred then EW_Term else Domain);

   begin
      T := Expr;
      N := First (Actions);
      while Present (N) loop
         case Nkind (N) is

            --  Currently ignore type declarations in actions. A more precise
            --  treatment would factor out the code of Transform_Declaration
            --  to possibly generate an assumption here.

            when N_Subtype_Declaration   |
                 N_Full_Type_Declaration =>
               null;

            when N_Object_Declaration =>
               declare
                  E : constant Entity_Id := Defining_Identifier (N);
               begin
                  pragma Assert (Constant_Present (N));

                  T :=
                    New_Typed_Binding
                      (Domain  => Subdomain,
                       Name    =>
                         New_Identifier (Name => Full_Name (E)),
                       Def     =>
                         +Transform_Expr
                         (Expression (N),
                          EW_Abstract (Etype (E)),
                          Subdomain,
                          Params),
                       Context => T);
               end;

            when N_Freeze_Entity =>
               null;

            when others =>
               raise Program_Error;
         end case;

         Next (N);
      end loop;

      return T;
   end Transform_Actions;

   -----------------------------------
   -- Transform_Actions_Preparation --
   -----------------------------------

   procedure Transform_Actions_Preparation
     (Actions : List_Id)
   is
      N  : Node_Id;
      Id : W_Identifier_Id;

   begin
      N := First (Actions);
      while Present (N) loop
         case Nkind (N) is

            --  Currently ignore type declarations in actions. A more precise
            --  treatment would factor out the code of Transform_Declaration
            --  to possibly generate an assumption here.

            when N_Subtype_Declaration   |
                 N_Full_Type_Declaration =>
               null;

            when N_Object_Declaration =>
               pragma Assert (Constant_Present (N));

               Id :=
                 New_Identifier
                   (Name => Full_Name (Defining_Identifier (N)),
                    Typ  => EW_Abstract (Etype (Defining_Identifier (N))));

               Insert_Entity
                 (Defining_Identifier (N),
                  Id);

            when N_Freeze_Entity =>
               null;

            when others =>
               raise Program_Error;
         end case;

         Next (N);
      end loop;
   end Transform_Actions_Preparation;

   -------------------------
   -- Transform_Aggregate --
   -------------------------

   function Transform_Aggregate
     (Params              : Transformation_Params;
      Domain              : EW_Domain;
      Expr                : Node_Id;
      In_Attribute_Update : Boolean := False) return W_Expr_Id
   is
      --  When the aggregate is the argument of a 'Update attribute_reference,
      --  get the prefix of the attribute_reference.

      Update_Prefix : constant Node_Id :=
        (if In_Attribute_Update then Prefix (Parent (Expr)) else Empty);

      -----------------------
      -- Local subprograms --
      -----------------------

      procedure Get_Aggregate_Elements
        (Expr         : Node_Id;
         Values       : out List_Of_Nodes.List;
         Types        : out List_Of_Nodes.List;
         Index_Values : out List_Of_Nodes.List;
         Index_Types  : out List_Of_Nodes.List);
      --  Extract parts of the aggregate Expr that will be passed in
      --  parameter to the logic function for the aggregate.
      --  Collect these parameters in Values, with the corresponding type
      --  stored at the same position in Types.
      --  For a normal aggregate each element of Values is an element of the
      --  (possibly multi-dimensional) aggregate.
      --  For a 'Update aggregate, the choice indexes are
      --  collected in Values in addition to the elements.
      --  Each element of Index_Values is a component_association whose
      --  choices need to be checked against the
      --  type at the same position in Index_Types.

      procedure Generate_Logic_Function
        (Expr   : Node_Id;
         Values : List_Of_Nodes.List;
         Types  : List_Of_Nodes.List);
      --  Generate the logic function definition for the aggregate Expr, with a
      --  suitable defining axiom:
      --
      --     function F (<params>) : <type of aggregate>
      --
      --     axiom A:
      --       forall id:<type of aggregate>. forall <params>.
      --         <proposition for the aggregate F(<params>)>

      function Transform_Array_Component_Associations
        (Expr   : Node_Id;
         Arr    : W_Expr_Id;
         Args   : Ada_Ent_To_Why.Map;
         Params : Transformation_Params) return W_Pred_Id;
      --  Generates the proposition defining the aggregate Arr, based on a
      --  mapping between Ada nodes and corresponding Why identifiers.

      function Complete_Translation
        (Params       : Transformation_Params;
         Domain       : EW_Domain;
         Func         : W_Identifier_Id;
         Values       : List_Of_Nodes.List;
         Types        : List_Of_Nodes.List;
         Index_Values : List_Of_Nodes.List;
         Index_Types  : List_Of_Nodes.List) return W_Expr_Id;
      --  Given a logic function Func previously defined for the aggregate,
      --  generate the actual call to Func by translating arguments Values
      --  of type Types in the context given by Params.

      --------------------------
      -- Complete_Translation --
      --------------------------

      function Complete_Translation
        (Params       : Transformation_Params;
         Domain       : EW_Domain;
         Func         : W_Identifier_Id;
         Values       : List_Of_Nodes.List;
         Types        : List_Of_Nodes.List;
         Index_Values : List_Of_Nodes.List;
         Index_Types  : List_Of_Nodes.List) return W_Expr_Id
      is
         pragma Assert (Values.Length /= 0);

         use List_Of_Nodes;

         Cnt   : Positive;
         Value : List_Of_Nodes.Cursor;
         Typ   : List_Of_Nodes.Cursor;
         Args  : W_Expr_Array (1 .. Integer (Values.Length));

         R : W_Expr_Id;

      begin
         --  Compute the arguments for the function call

         Cnt   := 1;
         Value := Values.First;
         Typ   := Types.First;
         while Value /= No_Element loop
            Args (Cnt) :=
              Transform_Expr
                (Element (Value),
                 EW_Abstract (Element (Typ)),
                 Domain,
                 Params);
            Next (Value);
            Next (Typ);
            Cnt := Cnt + 1;
         end loop;

         --  Compute the call

         R := New_Call (Ada_Node => Expr,
                        Domain   => Domain,
                        Name     => Func,
                        Args     => Args,
                        Typ      => EW_Abstract (Etype (Expr)));

         --  In programs, we generate a check that all the choices are
         --  compatible with their index subtype:
         --  . a non-static value of choice must belong to the index subtype
         --  . the range_constraint of a subtype_indication must be compatible
         --    with the given subtype.

         if Domain = EW_Prog then
            Value := Index_Values.First;
            Typ   := Index_Types.First;

            while Value /= No_Element loop
               R := +Sequence
                      (New_Ignore (Prog =>
                        +Transform_Discrete_Choices
                          (Choices      => Choices (Element (Value)),
                           Choice_Type  => Element (Typ),
                           Matched_Expr =>  --  The value does not matter here
                             New_Integer_Constant (Value => Uint_0),
                           Cond_Domain  => EW_Prog,
                           Params       => Params)),
                       +R);
               Next (Value);
               Next (Typ);
            end loop;
         end if;

         return R;
      end Complete_Translation;

      -----------------------------
      -- Generate_Logic_Function --
      -----------------------------

      procedure Generate_Logic_Function
        (Expr   : Node_Id;
         Values : List_Of_Nodes.List;
         Types  : List_Of_Nodes.List)
      is
         pragma Assert (Values.Length /= 0);

         use List_Of_Nodes;

         Expr_Typ   : constant Entity_Id  := Type_Of_Node (Expr);

         --  Generate name for the function based on the location of the
         --  aggregate.

         Name          : constant String := New_Temp_Identifier;
         Func          : constant W_Identifier_Id :=
                           New_Identifier (Name     => Name,
                                           Ada_Node => Expr);

         --  Predicate used to define the aggregate/updated object

         Params_No_Ref : constant Transformation_Params :=
                           (Theory      => Params.Theory,
                            File        => Params.File,
                            Phase       => Params.Phase,
                            Gen_Image   => False,
                            Ref_Allowed => False);

         --  Values used in calls to the aggregate function

         Ret_Type      : constant W_Type_Id :=
           EW_Abstract
             (if In_Attribute_Update then
                 Etype (Update_Prefix)
              else Expr_Typ);

         --  Arrays of binders and arguments, and mapping of nodes to names

         Call_Params   : Binder_Array (1 .. Integer (Values.Length));
         Call_Args     : W_Expr_Array (1 .. Integer (Values.Length));
         Args_Map      : Ada_Ent_To_Why.Map;

         --  Counter and iterators

         Cnt           : Positive;
         Value         : List_Of_Nodes.Cursor;
         Typ           : List_Of_Nodes.Cursor;

         --  Variables for the call, guard and proposition for the axiom

         Aggr          : W_Expr_Id;
         Def_Pred      : W_Pred_Id;

         Aggr_Temp     : constant W_Identifier_Id :=
           New_Temp_Identifier (Typ => Ret_Type);

         --  Select file for the declarations

         Decl_File     : Why_Section := Why_Sections (Dispatch_Entity (Expr));

      --  Start of Generate_Logic_Function

      begin
         --  Store the logic function

         Insert_Extra_Module (Expr,
                              New_Module
                                (File => No_Name,
                                 Name => NID (Name)));

         --  Compute the parameters/arguments for the axiom/call

         Cnt   := 1;
         Value := Values.First;
         Typ := Types.First;
         while Value /= No_Element loop
            declare
               Ident : constant W_Identifier_Id :=
                 New_Temp_Identifier (Typ => EW_Abstract (Element (Typ)));
               B     : constant Binder_Type :=
                 (Ada_Node => Empty,
                  B_Name   => Ident,
                  B_Ent    => null,
                  Mutable  => False);
            begin
               Call_Params (Cnt) := B;
               Call_Args (Cnt) := +Ident;

               --  Fill in mapping from Ada nodes to Why identifiers for the
               --  generation of the proposition in the defining axiom.

               Ada_Ent_To_Why.Insert (Args_Map, Element (Value), (Regular, B));

               Next (Typ);
               Next (Value);
               Cnt := Cnt + 1;
            end;
         end loop;

         --  Compute the call, guard and proposition for the axiom

         Aggr :=
           New_Call (Ada_Node => Expr,
                     Domain   => EW_Term,
                     Name     => Func,
                     Args     => Call_Args,
                     Typ      => EW_Abstract (Etype (Expr)));

         Def_Pred :=
           +New_Typed_Binding
             (Name   => Aggr_Temp,
              Domain => EW_Pred,
              Def    => Aggr,
              Context =>
                +Transform_Array_Component_Associations
                  (Expr   => Expr,
                   Arr    => +Aggr_Temp,
                   Args   => Args_Map,
                   Params => Params_No_Ref));

         --  Generate the necessary logic function and axiom declarations

         if Params.File = Decl_File.File then
            Decl_File.Cur_Theory := Why_Empty;
         end if;
         Open_Theory
           (Decl_File, Name,
            Comment =>
              "Module for defining the value of the "
                & (if In_Attribute_Update
                   then "update attribute"
                   else "aggregate")
                & " at "
                & (if Sloc (Expr) > 0 then
                      Build_Location_String (Sloc (Expr))
                   else "<no location>")
                & ", created in " & GNAT.Source_Info.Enclosing_Entity);

         Emit (Decl_File.Cur_Theory,
               New_Function_Decl (Domain      => EW_Term,
                                  Name        => Func,
                                  Labels      => Name_Id_Sets.Empty_Set,
                                  Binders     => Call_Params,
                                  Return_Type => Ret_Type));
         Emit (Decl_File.Cur_Theory,
               New_Guarded_Axiom (Name     => NID (Def_Axiom),
                                  Binders  => Call_Params,
                                  Triggers =>
                                    New_Triggers
                                      (Triggers =>
                                           (1 => New_Trigger
                                                (Terms => (1 => Aggr)))),
                                  Def      => Def_Pred));

         Close_Theory (Decl_File,
                       Kind => Definition_Theory,
                       Defined_Entity => Expr);
         if Params.File = Decl_File.File then
            Decl_File.Cur_Theory := Params.Theory;
         end if;
      end Generate_Logic_Function;

      ----------------------------
      -- Get_Aggregate_Elements --
      ----------------------------

      procedure Get_Aggregate_Elements
        (Expr         : Node_Id;
         Values       : out List_Of_Nodes.List;
         Types        : out List_Of_Nodes.List;
         Index_Values : out List_Of_Nodes.List;
         Index_Types  : out List_Of_Nodes.List)
      is
         Typ     : constant Entity_Id := Type_Of_Node (Expr);
         Num_Dim : constant Pos       := Number_Dimensions (Typ);

         -----------------------
         -- Local subprograms --
         -----------------------

         procedure Traverse_Value_At_Index
           (Dim                 : Pos;
            Index               : Node_Id;
            Expr_Or_Association : Node_Id);
         --  Traverse the value Expr_Or_Association to collect desired elements

         procedure Traverse_Rec_Aggregate
           (Dim   : Pos;
            Index : Node_Id;
            Expr  : Node_Id);
         --  Main recursive function operating over multi-dimensional array
         --  aggregates.

         -----------------------------
         -- Traverse_Value_At_Index --
         -----------------------------

         procedure Traverse_Value_At_Index
           (Dim                 : Pos;
            Index               : Node_Id;
            Expr_Or_Association : Node_Id)
         is
            Expr   : Node_Id;

            Choice : Node_Id;
            Rng    : Node_Id;

         begin
            --  Fill together the arrays Index_Values and Index_Types

            if Nkind (Expr_Or_Association) = N_Component_Association
              and then not Is_Others_Choice (Choices (Expr_Or_Association))
            then
               Index_Values.Append (Expr_Or_Association);
               Index_Types.Append (Etype (Index));

               --  For 'Update aggregates we also need the choices as
               --  parameters since they can be dynamic

               if In_Attribute_Update then

                  --  Collect the choices as parameters as well.
                  --  We cannot use Index_Values directly since they store
                  --  the whole associations. Instead, populate Values with
                  --  the parameters needed.

                  Choice := First (Choices (Expr_Or_Association));
                  while Present (Choice) loop
                     if Nkind (Choice) = N_Range then

                        --  The high and low bounds of a range both needs to
                        --  be parameters.

                        Rng := Get_Range (Choice);
                        Values.Append (Low_Bound (Rng));
                        Types.Append (Etype (Index));
                        Values.Append (High_Bound (Rng));
                        Types.Append (Etype (Index));
                     else
                        Values.Append (Choice);
                        Types.Append (Etype (Index));
                     end if;
                     Next (Choice);
                  end loop;
               end if;
            end if;

            --  Fill the component expression as well to the arrays
            --  Values and Types.
            if Nkind (Expr_Or_Association) = N_Component_Association
              and then Box_Present (Expr_Or_Association)
            then
               null;
            else
               Expr :=
                 (if Nkind (Expr_Or_Association) =
                    N_Component_Association
                  then
                    Expression (Expr_Or_Association)
                  else
                    Expr_Or_Association);

               if Dim < Num_Dim then
                  pragma Assert (Nkind (Expr) = N_Aggregate);
                  Traverse_Rec_Aggregate (Dim + 1, Next_Index (Index), Expr);
               else
                  declare
                     Exp_Type  : constant Node_Id := Component_Type (Typ);
                  begin
                     Values.Append (Expr);
                     Types.Append (Exp_Type);
                  end;
               end if;
            end if;
         end Traverse_Value_At_Index;

         ----------------------------
         -- Traverse_Rec_Aggregate --
         ----------------------------

         procedure Traverse_Rec_Aggregate
           (Dim   : Pos;
            Index : Node_Id;
            Expr  : Node_Id)
         is
            Exprs       : constant List_Id := Expressions (Expr);
            Assocs      : constant List_Id := Component_Associations (Expr);
            Expression  : Node_Id := Nlists.First (Exprs);
            Association : Node_Id := Nlists.First (Assocs);

         begin
            while Present (Expression) loop
               Traverse_Value_At_Index (Dim, Index, Expression);
               Next (Expression);
            end loop;

            --  Although named association is not allowed after positional
            --  association, an "others" case is allowed, and this is included
            --  in the list of associations, so we always do the following.

            while Present (Association) loop
               Traverse_Value_At_Index (Dim, Index, Association);
               Next (Association);
            end loop;
         end Traverse_Rec_Aggregate;

         --  Start of Get_Aggregate_Elements

      begin
         --  In the case of a 'Update attribute_reference, add the prefix to be
         --  a parameter to the logic function.

         if In_Attribute_Update then
            Values.Append (Update_Prefix);
            Types.Append (Etype (Update_Prefix));
         end if;

         Traverse_Rec_Aggregate (Dim   => 1,
                                 Index => First_Index (Typ),
                                 Expr  => Expr);
      end Get_Aggregate_Elements;

      --------------------------------------------
      -- Transform_Array_Component_Associations --
      --------------------------------------------

      function Transform_Array_Component_Associations
        (Expr   : Node_Id;
         Arr    : W_Expr_Id;
         Args   : Ada_Ent_To_Why.Map;
         Params : Transformation_Params) return W_Pred_Id
      is
         Typ     : constant Entity_Id := Type_Of_Node (Expr);
         Num_Dim : constant Pos := Number_Dimensions (Typ);
         Ind_Arr : array (1 .. Num_Dim) of Node_Id;
         Binders : W_Identifier_Array (1 .. Positive (Num_Dim));

         Indexes : W_Expr_Array (1 .. Positive (Num_Dim));
         --  This array contains either the identifiers for indexes in the
         --  normal translation, or the actual values of indexes in the
         --  translation for "simple" aggregates. For example, in the first
         --  case it could be:
         --     (tmp1, tmp2, tmp3)
         --  while in the second case it could be:
         --     (1, 3, 2)
         --  This allows using Constrain_Value_At_Index in both cases to get
         --  the value of the aggregate at the desired indexes.

         -----------------------
         -- Local subprograms --
         -----------------------

         type Transform_Rec_Func is access function
           (Dim  : Pos;
            Expr : Node_Id) return W_Expr_Id;
         --  Type of callback used to refer to either one of the recursive
         --  transformation functions for aggregate defined below, for use in
         --  Constrain_Value_At_Index.

         function Constrain_Value_At_Index
           (Dim                 : Pos;
            Expr_Or_Association : Node_Id;
            Callback            : Transform_Rec_Func) return W_Expr_Id;
         --  Return the proposition that the array at the given indices is
         --  equal to the value given in Expr_Or_Association, or else "true"
         --  for box association.

         function Is_Simple_Aggregate
           (Dim  : Pos;
            Expr : Node_Id) return Boolean;
         --  Detect whether aggregate Expr has no "others" or range choices, or
         --  multiple choices in an association.

         function Select_Nth_Index
           (Dim    : Pos;
            Offset : Nat) return W_Expr_Id;
         --  Return the value for Index at Offset from Id'First

         function Select_These_Choices
           (Dim : Pos;
            L   : List_Id) return W_Expr_Id;
         --  Return a proposition that expresses that Index satisfies one
         --  choice in the list of choices L. In the case of an aggregate of
         --  a 'Update attribute_reference, the (possibly dynamic) choices
         --  will be pulled from the arguments to the logic function.

         function Transform_Rec_Aggregate
           (Dim  : Pos;
            Expr : Node_Id) return W_Expr_Id;
         --  Main recursive function operating over multi-dimensional array
         --  aggregates.

         function Transform_Rec_Simple_Aggregate
           (Dim  : Pos;
            Expr : Node_Id) return W_Expr_Id;
         --  Specialized version of Transform_Rec_Aggregate when the aggregate
         --  is simple, as defined by Is_Simple_Aggregate.

         ------------------------------
         -- Constrain_Value_At_Index --
         ------------------------------

         function Constrain_Value_At_Index
           (Dim                 : Pos;
            Expr_Or_Association : Node_Id;
            Callback            : Transform_Rec_Func) return W_Expr_Id
         is
            --  Note that Expr_Or_Association here can be the prefix
            --  in the default case of the logic function of 'Update
            Expr : Node_Id;

         begin
            if Nkind (Expr_Or_Association) = N_Component_Association
              and then Box_Present (Expr_Or_Association)
            then
               return +True_Pred;
            else
               Expr :=
                 (if Nkind (Expr_Or_Association) =
                    N_Component_Association
                  then
                     Expression (Expr_Or_Association)
                  else
                     Expr_Or_Association);

               if Dim < Num_Dim then
                  pragma Assert (Nkind (Expr) = N_Aggregate);
                  return Callback (Dim + 1, Expr);
               else
                  declare
                     Arg_Val : constant W_Expr_Id :=
                       +Ada_Ent_To_Why.Element (Args, Expr).Main.B_Name;
                     Value   : W_Expr_Id;
                     Read    : W_Expr_Id;
                  begin
                     --  Special case for the prefix of the 'Update
                     --  attribute_reference. In that case, we want to build
                     --  the value Prefix(i,j..) with the default indexes.

                     if In_Attribute_Update and then Expr = Update_Prefix then
                        Value := New_Array_Access (Ada_Node => Empty,
                                                   Domain   => EW_Term,
                                                   Ar       => Arg_Val,
                                                   Index    => Indexes);

                     else
                        Value := Arg_Val;
                     end if;

                     Read := New_Array_Access (Ada_Node => Expr_Or_Association,
                                               Domain   => EW_Term,
                                               Ar       => Arr,
                                               Index    => Indexes);
                     return New_Comparison (Cmp    => EW_Eq,
                                            Left   => Read,
                                            Right  => Value,
                                            Domain => EW_Pred);
                  end;
               end if;
            end if;
         end Constrain_Value_At_Index;

         -------------------------
         -- Is_Simple_Aggregate --
         -------------------------

         function Is_Simple_Aggregate
           (Dim  : Pos;
            Expr : Node_Id) return Boolean
         is
            Exprs       : constant List_Id := Expressions (Expr);
            Assocs      : constant List_Id := Component_Associations (Expr);
            Association : Node_Id;
            Expression  : Node_Id;

            Is_Simple : Boolean := True;

            procedure Check_Simple (B : Boolean);
            --  Take into account the intermediate check B

            ------------------
            -- Check_Simple --
            ------------------

            procedure Check_Simple (B : Boolean) is
            begin
               Is_Simple := B and Is_Simple;
            end Check_Simple;

         begin
            Expression  := Nlists.First (Exprs);
            Association := Nlists.First (Assocs);

            while Present (Expression) loop
               --  For multi-dimensional aggregates, recurse

               if Dim < Num_Dim then
                  pragma Assert (Nkind (Expression) = N_Aggregate);
                  Check_Simple (Is_Simple_Aggregate (Dim + 1, Expression));
               end if;
               Next (Expression);
            end loop;

            while Present (Association) loop

               --  Check that there is only one choice, and it is neither a
               --  range not a dynamic value.

               declare
                  Only_Choice : constant Node_Id :=
                                  First (Choices (Association));
               begin
                  Check_Simple
                    (List_Length (Choices (Association)) = 1
                      and then not Discrete_Choice_Is_Range (Only_Choice)
                      and then Compile_Time_Known_Value (Only_Choice));
               end;

               --  For multi-dimensional aggregates, recurse

               Expression := Sinfo.Expression (Association);

               if Dim < Num_Dim then
                  pragma Assert (Nkind (Expression) = N_Aggregate);
                  Check_Simple (Is_Simple_Aggregate (Dim + 1, Expression));
               end if;

               Next (Association);
            end loop;

            return Is_Simple;
         end Is_Simple_Aggregate;

         ----------------------
         -- Select_Nth_Index --
         ----------------------

         function Select_Nth_Index
           (Dim    : Pos;
            Offset : Nat) return W_Expr_Id
         is
            Rng        : constant Node_Id := Get_Range (Ind_Arr (Dim));
            Low        : constant Node_Id := Low_Bound (Rng);
            First, Val : W_Expr_Id;

         begin

            if Is_Static_Expression (Low) then
               Val := New_Integer_Constant
                 (Value => Expr_Value (Low) + UI_From_Int (Offset));

            else
               First := New_Attribute_Expr (Etype (Rng), Attribute_First);

               Val := New_Binary_Op
                        (Left     => First,
                         Right    =>
                          New_Integer_Constant (Value => UI_From_Int (Offset)),
                         Op       => EW_Add,
                         Op_Type  => EW_Int);
            end if;

            return Val;
         end Select_Nth_Index;

         --------------------------
         -- Select_These_Choices --
         --------------------------

         function Select_These_Choices
           (Dim : Pos;
            L   : List_Id) return W_Expr_Id
         is
            Result     : W_Expr_Id := +False_Pred;
            Choice     : Node_Id := First (L);
            Rng_Expr   : W_Expr_Id;
            Low        : Node_Id;
            High       : Node_Id;
            Arg_Low    : W_Expr_Id;
            Arg_High   : W_Expr_Id;
            Arg_Choice : W_Expr_Id;
         begin
            while Present (Choice) loop
               if In_Attribute_Update then
                  if Nkind (Choice) = N_Range then
                     Low        := Low_Bound (Get_Range (Choice));
                     High       := High_Bound (Get_Range (Choice));

                     Arg_Low :=
                       +Ada_Ent_To_Why.Element (Args, Low).Main.B_Name;
                     Arg_Low :=
                       Insert_Simple_Conversion (Domain => EW_Term,
                                                 Expr   => Arg_Low,
                                                 To     => EW_Int_Type);
                     Arg_High :=
                       +Ada_Ent_To_Why.Element (Args, High).Main.B_Name;

                     Arg_High :=
                       Insert_Simple_Conversion (Domain => EW_Term,
                                                 Expr   => Arg_High,
                                                 To     => EW_Int_Type);
                     Rng_Expr :=
                       New_Range_Expr (Domain    => EW_Pred,
                                       Low       => Arg_Low,
                                       High      => Arg_High,
                                       Expr      => Indexes (Integer (Dim)));
                  else
                     Arg_Choice :=
                       +Ada_Ent_To_Why.Element (Args, Choice).Main.B_Name;
                     Arg_Choice :=
                       Insert_Simple_Conversion (Domain => EW_Term,
                                                 Expr   => Arg_Choice,
                                                 To     => EW_Int_Type);
                     Rng_Expr :=
                       New_Comparison (Cmp    => EW_Eq,
                                       Left   => Indexes (Integer (Dim)),
                                       Right  => Arg_Choice,
                                       Domain => EW_Pred);

                  end if;
               else
                  --  The choices are not arguments, proceed with standard
                  --  transformation of discrete choice
                  Rng_Expr :=
                    Transform_Discrete_Choice
                      (Choice      => Choice,
                       Choice_Type => Empty,
                       Expr        => Indexes (Integer (Dim)),
                       Domain      => EW_Pred,
                       Params      => Params);
               end if;

               Result := New_Or_Expr (Left   => Result,
                                      Right  => Rng_Expr,
                                      Domain => EW_Pred);
               Next (Choice);
            end loop;
            return Result;
         end Select_These_Choices;

         -----------------------------
         -- Transform_Rec_Aggregate --
         -----------------------------

         function Transform_Rec_Aggregate
           (Dim  : Pos;
            Expr : Node_Id) return W_Expr_Id
         is
            Callback : constant Transform_Rec_Func :=
                         Transform_Rec_Aggregate'Access;
            Exprs    : constant List_Id := Expressions (Expr);
            Assocs   : constant List_Id := Component_Associations (Expr);

            Association     : Node_Id;
            Expression      : Node_Id;
            Else_Part       : W_Expr_Id := +True_Pred;
            Assocs_Len      : Nat;

         begin
            Assocs_Len := List_Length (Assocs);
            --  Starting with last association
            Association :=
              (if Nlists.Is_Empty_List (Assocs) then Empty
               else Nlists.Last (Assocs));

            --  First, generate else part:
            if Present (Association) then
               if In_Attribute_Update then

                  --  Setting up for 'Update transformation/axiom generation...

                  --  For 'Update we always want a default value in
                  --  the logic function so populate the else part properly.
                  --  Send the Prefix in to use for default value in the
                  --  logic function.
                  Else_Part :=
                    Constrain_Value_At_Index (Dim, Update_Prefix, Callback);

                  --  Next, constructing else part for a "normal" aggregate,
                  --  special case for "others" choice...
               elsif (List_Length (Choices (Association)) = 1
                        and then
                        --  case of "others" choice
                        Nkind (First (Choices (Association))) =
                        N_Others_Choice)
                 or else
                 --  case of a single association
                 Assocs_Len = 1
               then
                  --  Special case for "others" choice, which must
                  --  appear alone as last association. This case also
                  --  deals with a single association, wich may be
                  --  useful when an "others" dynamic range is
                  --  represented using X'Range or X'First..X'Last or
                  --  X, which should not be translated as
                  --  such. Indeed, these reference variable X which
                  --  is not known in the context of the proposition
                  --  generated here.
                  if not Box_Present (Association) then
                     Else_Part :=
                       Constrain_Value_At_Index (Dim, Association, Callback);
                  end if;
                  --  Dropping this single (and thus last) element.
                  Prev (Association);
                  Assocs_Len := Assocs_Len - 1;
               else
                  --  default else part for a normal aggregate
                  Else_Part := +True_Pred;
               end if;
            end if;

            Expression :=
              (if Nlists.Is_Empty_List (Exprs) then
                  Empty
               else
                  Nlists.Last (Exprs));

            if Present (Expression) then
               pragma Assert (No (Association));

               declare
                  Elsif_Parts : W_Expr_Array
                    (1 .. Integer (List_Length (Exprs)) - 1);
               begin
                  for Offset in reverse 1 .. List_Length (Exprs) - 1 loop
                     Elsif_Parts (Integer (Offset)) := New_Elsif
                       (Domain    => EW_Pred,
                        Condition =>
                          +New_Comparison
                            (Cmp       => EW_Eq,
                             Left      => Indexes (Integer (Dim)),
                             Right     => Select_Nth_Index (Dim, Offset),
                             Domain    => EW_Pred),
                        Then_Part =>
                          Constrain_Value_At_Index
                            (Dim, Expression, Callback));
                     Prev (Expression);
                  end loop;

                  return New_Conditional
                    (Domain      => EW_Pred,
                     Condition   =>
                       +New_Comparison
                         (Cmp       => EW_Eq,
                          Left      => Indexes (Integer (Dim)),
                          Right     => Select_Nth_Index (Dim, 0),
                          Domain    => EW_Pred),
                     Then_Part   =>
                       Constrain_Value_At_Index (Dim, Expression, Callback),
                     Elsif_Parts => Elsif_Parts,
                     Else_Part   => Else_Part);
               end;

            elsif Present (Association) then
               --  This either empty, or still at the last association
               --  (second from last if we have chopped off an others)

               declare
                  Condition   : W_Expr_Id;
                  Then_Part   : W_Expr_Id;
                  Elsif_Parts : W_Expr_Array (1 .. Integer (Assocs_Len) - 1);
               begin
                  --  The conditional in the logic function axiom must be
                  --  generated in the reverse order of the associations
                  --  for 'Update semantics which allows duplicate choices.
                  --  For a normal aggregate this order does not matter since
                  --  they cannot have overlapping choices. So we share this
                  --  implementation.
                  --
                  --  Generate If condition and Then part:
                  --
                  --  The first condition (if) in the axiom corresponds to
                  --  the last association:
                  Condition := +Select_These_Choices (Dim,
                                                      Choices (Association));
                  Then_Part := Constrain_Value_At_Index (Dim,
                                                         Association,
                                                         Callback);
                  Prev (Association);
                  if Present (Association) then
                     --  If we have any more associations they go into
                     --  the elsif branches, in reverse order:

                     for Offset in reverse 1 .. Assocs_Len - 1 loop
                        --  Loop to generate Elsif Then parts.

                        --  Store in reverse order here (Assocs_Len - Offset)
                        Elsif_Parts (Integer (Assocs_Len - Offset)) :=
                          New_Elsif
                          (Domain    => EW_Pred,
                           Condition =>
                             +Select_These_Choices
                               (Dim, Choices (Association)),
                           Then_Part =>
                             Constrain_Value_At_Index
                             (Dim, Association, Callback));
                        Prev (Association);
                     end loop;
                  end if;

                  --  Finally, generate the whole ITE
                  return
                    New_Conditional (Domain      => EW_Pred,
                                     Condition   => Condition,
                                     Then_Part   => Then_Part,
                                     Elsif_Parts => Elsif_Parts,
                                     Else_Part   => Else_Part);
               end;
            else
               return Else_Part;
            end if;
         end Transform_Rec_Aggregate;

         ------------------------------------
         -- Transform_Rec_Simple_Aggregate --
         ------------------------------------

         function Transform_Rec_Simple_Aggregate
           (Dim  : Pos;
            Expr : Node_Id) return W_Expr_Id
         is
            Callback    : constant Transform_Rec_Func :=
                            Transform_Rec_Simple_Aggregate'Access;
            Exprs       : constant List_Id := Expressions (Expr);
            Assocs      : constant List_Id := Component_Associations (Expr);
            Association : Node_Id;
            Expression  : Node_Id;

         begin
            Expression  := Nlists.First (Exprs);
            Association := Nlists.First (Assocs);

            if Present (Expression) then
               pragma Assert (No (Association));

               declare
                  Conjuncts : W_Expr_Array
                    (1 .. Integer (List_Length (Exprs)));
               begin
                  for Offset in 1 .. List_Length (Exprs) loop
                     Indexes (Integer (Dim)) :=
                       Select_Nth_Index (Dim, Offset - 1);
                     Conjuncts (Integer (Offset)) :=
                       Constrain_Value_At_Index (Dim, Expression, Callback);
                     Next (Expression);
                  end loop;

                  return New_And_Expr (Domain    => EW_Pred,
                                       Conjuncts => Conjuncts);
               end;

            else
               pragma Assert (Present (Association));

               declare
                  Conjuncts : W_Expr_Array
                    (1 .. Integer (List_Length (Assocs)));
               begin
                  for Offset in 1 .. List_Length (Assocs) loop
                     pragma Assert (List_Length (Choices (Association)) = 1);
                     Indexes (Integer (Dim)) :=
                       Transform_Expr (Expr          =>
                                         First (Choices (Association)),
                                       Expected_Type => EW_Int_Type,
                                       Domain        => EW_Term,
                                       Params        => Params);
                     Conjuncts (Integer (Offset)) :=
                       Constrain_Value_At_Index (Dim, Association, Callback);
                     Next (Association);
                  end loop;

                  return New_And_Expr (Domain    => EW_Pred,
                                       Conjuncts => Conjuncts);
               end;
            end if;
         end Transform_Rec_Simple_Aggregate;

      --  Start of Transform_Array_Component_Associations

      begin
         --  Fill the array of index nodes

         Ind_Arr (1) := First_Index (Typ);
         for Dim in 2 .. Num_Dim loop
            Ind_Arr (Dim) := Next_Index (Ind_Arr (Dim - 1));
         end loop;

         --  Define index variables

         for J in 1 .. Integer (Num_Dim) loop
            Binders (J) := New_Temp_Identifier (Typ => EW_Int_Type);
            Indexes (J) := +Binders (J);
         end loop;

         --  Create the proposition defining the aggregate

         if not In_Attribute_Update
           and then Is_Simple_Aggregate (Dim => 1, Expr => Expr)
         then
            return +Transform_Rec_Simple_Aggregate (Dim => 1, Expr => Expr);
         else
            return New_Universal_Quantif
              (Variables => Binders,
               Var_Type  => +EW_Int_Type,
               Labels      => Name_Id_Sets.Empty_Set,
               Pred      => +Transform_Rec_Aggregate (Dim => 1, Expr => Expr));
         end if;
      end Transform_Array_Component_Associations;

      --  Elements of the aggregate

      Values       : List_Of_Nodes.List;
      Types        : List_Of_Nodes.List;
      Index_Values : List_Of_Nodes.List;
      Index_Types  : List_Of_Nodes.List;

   --  Start of Transform_Aggregate

   begin
      --  Get the aggregate elements that should be passed in parameter

      Get_Aggregate_Elements
        (Expr, Values, Types, Index_Values, Index_Types);

      --  If not done already, generate the logic function

      declare
         M : W_Module_Id := E_Module (Expr);
      begin
         if M = Why_Empty then
            Generate_Logic_Function (Expr, Values, Types);
            M := E_Module (Expr);
         end if;
         return
           Complete_Translation
             (Params,
              Domain,
              New_Identifier
                (Ada_Node => Expr,
                 Domain   => Domain,
                 Module   => M,
                 Symbol   => Get_Name (M)),
              Values,
              Types,
              Index_Values,
              Index_Types);
      end;
   end Transform_Aggregate;

   --------------------------------
   -- Transform_Array_Comparison --
   --------------------------------

   function Transform_Array_Comparison
     (Params : Transformation_Params;
      Expr   : Node_Id;
      Domain : EW_Domain) return W_Expr_Id
   is
      Left      : constant Node_Id := Left_Opnd (Expr);
      Right     : constant Node_Id := Right_Opnd (Expr);
      Subdomain : constant EW_Domain :=
        (if Domain = EW_Pred then EW_Term else Domain);
      Args      : W_Expr_Array (1 .. 6);
      T         : W_Expr_Id;
      Left_Expr : constant W_Expr_Id :=
        New_Temp_For_Expr (Transform_Expr (Left, Subdomain, Params));
      Right_Expr : constant W_Expr_Id :=
        New_Temp_For_Expr (Transform_Expr (Right, Subdomain, Params));
      Arg_Ind    : Positive := 1;
   begin
      Add_Array_Arg (Subdomain, Args, Left_Expr, Arg_Ind);
      Add_Array_Arg (Subdomain, Args, Right_Expr, Arg_Ind);
      T :=
        New_Call
          (Ada_Node => Expr,
           Domain   => Subdomain,
           Name     =>
             Prefix
               (Ada_Node => Etype (Left),
                M        =>
                  Array_Modules
                    (Positive (Number_Dimensions (Type_Of_Node (Left)))),
                W        => WNE_Array_Compare),
           Args     => Args,
           Typ      => EW_Int_Type);
      T := Binding_For_Temp (Domain  => Domain,
                             Tmp     => Left_Expr,
                             Context => T);
      T := Binding_For_Temp (Domain  => Domain,
                             Tmp     => Right_Expr,
                             Context => T);
      T := New_Comparison
        (Cmp       => Transform_Compare_Op (Nkind (Expr)),
         Left      => T,
         Right     =>
           New_Integer_Constant (Value  => Uint_0),
         Domain    => Domain);
      return T;
   end Transform_Array_Comparison;

   ------------------------------
   -- Transform_Array_Equality --
   ------------------------------

   function Transform_Array_Equality
     (Params : Transformation_Params;
      Expr   : Node_Id;
      Domain : EW_Domain) return W_Expr_Id
   is
      Left      : constant Node_Id := Left_Opnd (Expr);
      Right     : constant Node_Id := Right_Opnd (Expr);
      Left_Ty   : constant Entity_Id := Etype (Left);
      Dim       : constant Positive := Positive (Number_Dimensions (Left_Ty));
      Subdomain : constant EW_Domain :=
        (if Domain = EW_Pred then EW_Term else Domain);
      Args      : W_Expr_Array (1 .. 4 * Dim + 2);
      T         : W_Expr_Id;
      Left_Expr : constant W_Expr_Id :=
        New_Temp_For_Expr (Transform_Expr (Left, Subdomain, Params));
      Right_Expr : constant W_Expr_Id :=
        New_Temp_For_Expr (Transform_Expr (Right, Subdomain, Params));
      Arg_Ind    : Positive := 1;
   begin
      Add_Array_Arg (Subdomain, Args, Left_Expr, Arg_Ind);
      Add_Array_Arg (Subdomain, Args, Right_Expr, Arg_Ind);
      T :=
        New_Call
          (Ada_Node => Expr,
           Domain   => Subdomain,
           Name     =>
             Prefix
               (M        =>
                  Array_Modules
                    (Positive (Number_Dimensions (Type_Of_Node (Left)))),
                W        => WNE_Bool_Eq),
           Args     => Args,
           Typ      => EW_Bool_Type);
      T := Binding_For_Temp (Domain  => Domain,
                             Tmp     => Left_Expr,
                             Context => T);
      T := Binding_For_Temp (Domain  => Domain,
                             Tmp     => Right_Expr,
                             Context => T);
      if Domain = EW_Pred then
         T := New_Comparison
           (Cmp       => Transform_Compare_Op (Nkind (Expr)),
            Left      => T,
            Right     => New_Literal (Domain => Subdomain,
                                      Value  => EW_True),
            Domain    => Domain);
      elsif Nkind (Expr) = N_Op_Ne then
         T :=
           New_Call (Domain => Domain,
                     Name   => To_Ident (WNE_Bool_Not),
                     Args   => (1 => T),
                     Typ    => EW_Bool_Type);
      end if;
      return T;
   end Transform_Array_Equality;

   --------------------------------
   -- Transform_Array_Logical_Op --
   --------------------------------

   function Transform_Array_Logical_Op
     (Params   : Transformation_Params;
      Expr     : Node_Id;
      Domain   : EW_Domain;
      Do_Check : Boolean) return W_Expr_Id
   is
      Left      : constant Node_Id := Left_Opnd (Expr);
      Right     : constant Node_Id := Right_Opnd (Expr);
      Left_Ty   : constant Entity_Id := Etype (Left);
      Subdomain : constant EW_Domain :=
        (if Domain = EW_Pred then EW_Term else Domain);
      Args      : W_Expr_Array (1 .. 6);
      T         : W_Expr_Id;
      Arg_Ind   : Positive := 1;
      Left_Expr : constant W_Expr_Id :=
        New_Temp_For_Expr (Transform_Expr (Left, Subdomain, Params));
      Right_Expr : constant W_Expr_Id :=
        New_Temp_For_Expr (Transform_Expr (Right, Subdomain, Params));
      Op         : constant Why_Name_Enum :=
        (case Nkind (Expr) is
            when N_Op_And => WNE_Bool_And,
            when N_Op_Or  => WNE_Bool_Or,
            when others   => WNE_Bool_Xor);

      Left_Length  : constant W_Expr_Id :=
        Build_Length_Expr (Domain => EW_Term, Expr => Left_Expr, Dim => 1);
      Right_Length : constant W_Expr_Id :=
        Build_Length_Expr (Domain => EW_Term, Expr => Right_Expr, Dim => 1);
      Length_Check : constant W_Expr_Id :=
        New_Relation
          (Domain  => EW_Pred,
           Op_Type => EW_Int,
           Op      => EW_Eq,
           Left    => +Left_Length,
           Right   => +Right_Length);

      --  if Length (Left) > 0 then not (Left'First = Left'Last and
      --                                 Left'Last  = 1);
      Range_Check  : constant W_Expr_Id :=
        New_Conditional
          (Domain    => EW_Pred,
           Condition =>
             New_Relation
               (Domain  => EW_Pred,
                Op_Type => EW_Int,
                Op      => EW_Gt,
                Left    => +Left_Length,
                Right   => New_Integer_Constant (Value => Uint_0)),
           Then_Part =>
             New_Not
               (Domain   => EW_Pred,
                Right    =>
                  New_And_Expr
                    (Left   => New_Relation
                       (Domain  => EW_Pred,
                        Op_Type => EW_Int,
                        Op      => EW_Eq,
                        Left    =>
                          +Prefix
                          (M =>
                               E_Module (Component_Type (Left_Ty)),
                           W => WNE_Attr_First),
                        Right   =>
                          +Prefix
                          (M =>
                               E_Module (Component_Type (Left_Ty)),
                           W => WNE_Attr_Last)),
                     Right  => New_Relation
                       (Domain  => EW_Pred,
                        Op_Type => EW_Int,
                        Op      => EW_Eq,
                        Left    => New_Integer_Constant (Value => Uint_1),
                        Right   =>
                          +Prefix
                          (M =>
                               E_Module (Component_Type (Left_Ty)),
                           W => WNE_Attr_Last)),
                       Domain => EW_Pred)));
   begin
      Add_Array_Arg (Subdomain, Args, Left_Expr, Arg_Ind);
      Add_Array_Arg (Subdomain, Args, Right_Expr, Arg_Ind);

      --  Call to operator

      T :=
        New_Call
          (Ada_Node => Expr,
           Domain   => Subdomain,
           Name     =>
             Prefix
               (M        =>
                  Array_Modules (1),
                W        => Op),
           Args     => Args);

      if Do_Check then

         --  Length check, Left and Right should have the same length

         T := +Sequence (New_Ignore (Prog => New_Located_Assert (Expr,
                                     +Length_Check,
                                     VC_Length_Check)),
                         +T);

         --  Range check : for all I, Left (I) Op Right (I) should be in range.
         --  The only way to generate an element not in range using a binary
         --  operator is to call xor on arrays of the singleton subtype True of
         --  boolean.

         if not Is_Standard_Boolean_Type (Component_Type (Left_Ty)) and then
           Op = WNE_Bool_Xor
         then
            T :=  +Sequence (New_Ignore (Prog => New_Located_Assert (Expr,
                                         +Range_Check,
                                         VC_Range_Check)),
                             +T);
         end if;
      end if;

      --  Conversion from base, first and right are attributes of left

      T := Array_Convert_From_Base
        (Domain => Subdomain,
         Target => Left_Ty,
         Ar     => T,
         First  =>
           Get_Array_Attr (Domain => Subdomain,
                           Expr   => Left_Expr,
                           Attr   => Attribute_First,
                           Dim    => 1),
         Last   =>
           Get_Array_Attr (Domain => Subdomain,
                           Expr   => Left_Expr,
                           Attr   => Attribute_Last,
                           Dim    => 1));

      T := Binding_For_Temp (Domain  => Domain,
                             Tmp     => Left_Expr,
                             Context => T);
      T := Binding_For_Temp (Domain  => Domain,
                             Tmp     => Right_Expr,
                             Context => T);
      return T;
   end Transform_Array_Logical_Op;

   ------------------------------
   -- Transform_Array_Negation --
   ------------------------------

   function Transform_Array_Negation
     (Params   : Transformation_Params;
      Expr     : Node_Id;
      Domain   : EW_Domain;
      Do_Check : Boolean) return W_Expr_Id
   is
      Right     : constant Node_Id := Right_Opnd (Expr);
      Right_Ty  : constant Entity_Id := Etype (Expr);
      Subdomain : constant EW_Domain :=
        (if Domain = EW_Pred then EW_Term else Domain);
      Args      : W_Expr_Array (1 .. 3);
      T         : W_Expr_Id;
      Arg_Ind   : Positive := 1;
      Right_Expr : constant W_Expr_Id :=
        New_Temp_For_Expr (Transform_Expr (Right, Subdomain, Params));

      Right_Length : constant W_Expr_Id :=
        Build_Length_Expr (Domain => EW_Term, Expr => Right_Expr, Dim => 1);
      Range_Check  : constant W_Expr_Id :=
        New_Conditional
          (Domain    => EW_Pred,
           Condition =>
             New_Relation
               (Domain  => EW_Pred,
                Op_Type => EW_Int,
                Op      => EW_Gt,
                Left    => +Right_Length,
                Right   => New_Integer_Constant (Value => Uint_0)),
           Then_Part => New_Relation
             (Domain  => EW_Pred,
              Op_Type => EW_Int,
              Op      => EW_Lt,
              Left    =>
                +Prefix
                (M =>
                     E_Module (Component_Type (Right_Ty)),
                 W => WNE_Attr_First),
              Right   =>
                +Prefix
                (M =>
                     E_Module (Component_Type (Right_Ty)),
                 W => WNE_Attr_Last)));
   begin
      Add_Array_Arg (Subdomain, Args, Right_Expr, Arg_Ind);

      --  Call to operator

      T :=
        New_Call
          (Ada_Node => Expr,
           Domain   => Subdomain,
           Name     =>
             Prefix
               (M => Array_Modules (1),
                N => "notb"),
           Args     => Args);

      if Do_Check then

         --  Range check : for all I, Not Right (I) should be in range.
         --  The only way to generate an element not in range using negation
         --  is to call it on an array of a singleton subtype of boolean.

         if not Is_Standard_Boolean_Type (Component_Type (Right_Ty)) then
            T :=  +Sequence (New_Ignore (Prog => New_Located_Assert (Expr,
                                         +Range_Check,
                                         VC_Range_Check)),
                             +T);
         end if;
      end if;

      --  Conversion from base

      T := Array_Convert_From_Base
        (Domain => Subdomain,
         Target => Right_Ty,
         Ar     => T,
         First  =>
           Get_Array_Attr (Domain => Subdomain,
                           Expr   => Right_Expr,
                           Attr   => Attribute_First,
                           Dim    => 1),
         Last   =>
           Get_Array_Attr (Domain => Subdomain,
                           Expr   => Right_Expr,
                           Attr   => Attribute_Last,
                           Dim    => 1));

      T := Binding_For_Temp (Domain  => Domain,
                             Tmp     => Right_Expr,
                             Context => T);
      return T;
   end Transform_Array_Negation;

   ---------------------
   -- Transform_Slice --
   ---------------------

   function Transform_Slice
     (Params       : Transformation_Params;
      Domain       : EW_Domain;
      Expr         : Node_Id) return W_Expr_Id
   is

      Prefx     : constant Node_Id := Sinfo.Prefix (Expr);
      Target_Ty : constant W_Type_Id := EW_Abstract (Etype (Expr));
      Rng       : constant Node_Id := Get_Range (Discrete_Range (Expr));
      Pref_Expr : W_Expr_Id;
      T         : W_Expr_Id;
      Low_Expr  : constant W_Expr_Id :=
        New_Temp_For_Expr
          (Transform_Expr (Low_Bound (Rng), EW_Int_Type, Domain, Params));
      High_Expr  : constant W_Expr_Id :=
        New_Temp_For_Expr
          (Transform_Expr (High_Bound (Rng), EW_Int_Type, Domain, Params));
   begin

      --  We start by translating the prefix itself.

      Pref_Expr :=
        Transform_Expr (Prefx, Domain, Params);

      --  in the case where the slice indices are static, we can simply deal
      --  with the array contents, and bounds will be derived from the type

      if Is_Static_Array_Type (Etype (Expr)) then

         --  a conversion may be needed to the target type

         T :=
           Insert_Array_Conversion
             (Domain => Domain,
              Expr   => Pref_Expr,
              To     => Target_Ty);

      --  when the slice bounds are not static, we produce a compound object
      --  contents + bounds.

      else
         Pref_Expr := New_Temp_For_Expr (Pref_Expr);
         T := Pref_Expr;

         if not Is_Static_Array_Type (Get_Ada_Node (+Get_Type (Pref_Expr)))
           and then Get_Base_Type (Get_Type (Pref_Expr)) /= EW_Split
         then
            T := Array_Convert_To_Base (Domain, Pref_Expr);
         end if;

         if Domain = EW_Prog then
            declare
               Ar_Low   : constant W_Expr_Id :=
                 Get_Array_Attr (Domain => EW_Pred,
                                 Expr   => Pref_Expr,
                                 Attr   => Attribute_First,
                                 Dim    => 1);
               Ar_High  : constant W_Expr_Id :=
                 Get_Array_Attr (Domain => EW_Pred,
                                 Expr   => Pref_Expr,
                                 Attr   => Attribute_Last,
                                 Dim    => 1);
               Check    : constant W_Pred_Id :=
                 New_Connection
                   (Op     => EW_Imply,
                    Left   =>
                      New_Relation (Domain  => EW_Pred,
                                    Op_Type => EW_Int,
                                    Op      => EW_Le,
                                    Left    => Low_Expr,
                                    Right   => High_Expr),
                    Right  =>
                      New_And_Then_Expr
                        (Domain => EW_Pred,
                         Left   =>
                           New_Relation
                             (Domain  => EW_Pred,
                              Op_Type => EW_Int,
                              Op      => EW_Le,
                              Left    => +Ar_Low,
                              Right   => Low_Expr,
                              Op2     => EW_Le,
                              Right2  => +Ar_High),
                         Right =>
                           New_Relation
                             (Domain  => EW_Pred,
                              Op_Type => EW_Int,
                              Op      => EW_Le,
                              Left    => +Ar_Low,
                              Right   => +High_Expr,
                              Op2     => EW_Le,
                              Right2  => +Ar_High)));
            begin
               T :=
                 +Sequence
                 (New_Located_Assert (Expr, Check, VC_Range_Check), +T);
            end;
         end if;

         T :=
           Binding_For_Temp
             (Domain  => Domain,
              Tmp     => Pref_Expr,
              Context => T);
         T :=
           Array_Convert_From_Base
             (Domain => Domain,
              Ar     => T,
              Target => Get_Ada_Node (+Target_Ty),
              First  => Low_Expr,
              Last   => High_Expr);
         T :=
           Binding_For_Temp
             (Domain  => Domain,
              Tmp     => Low_Expr,
              Context => T);
         T :=
           Binding_For_Temp
             (Domain  => Domain,
              Tmp     => High_Expr,
              Context => T);
      end if;

      return T;
   end Transform_Slice;

   ------------------------------------
   -- Transform_Assignment_Statement --
   ------------------------------------

   function Transform_Assignment_Statement (Stmt : Node_Id) return W_Prog_Id
   is
      Lvalue   : constant Node_Id := Name (Stmt);
      Exp_Entity : constant W_Type_Id := Expected_Type_Of_Prefix (Lvalue);
      L_Type   : constant W_Type_Id :=
        EW_Abstract (Etype (Lvalue));
      T        : W_Prog_Id :=
        +Transform_Expr
        (Expression (Stmt),
         L_Type,
         EW_Prog,
         Params => Body_Params);
      Need_Check : constant Boolean :=
        Present (Get_Ada_Node (+L_Type)) and then
        Is_Array_Type (Get_Ada_Node (+L_Type)) and then
        not Is_Static_Array_Type (Get_Ada_Node (+L_Type));
      Tmp      : constant W_Expr_Id :=
        New_Temp_For_Expr (+T, Need_Check);
   begin

      --  The Exp_Entity type is in fact the type that is expected in Why.
      --  The L_Type is a more precise type entity in Ada. We have to
      --  respect both constraints here, so we first convert to the Ada type
      --  (to get checks), and then convert to Why (without checks) to get the
      --  types right.

      if Need_Check then
         declare
            Check : W_Pred_Id := True_Pred;
            Lval  : constant W_Expr_Id :=
              New_Temp_For_Expr (Transform_Expr (Lvalue, EW_Term, Body_Params),
                                 True);
            Dim   : constant Positive :=
              Positive (Number_Dimensions (Get_Ada_Node (+L_Type)));
         begin
            for I in 1 .. Dim loop
               declare
                  Input_Length    : constant W_Expr_Id :=
                    Build_Length_Expr (EW_Term, Tmp, I);
                  Expected_Length : constant W_Expr_Id :=
                    Build_Length_Expr (EW_Term, Lval, I);
               begin
                  Check :=
                    +New_And_Then_Expr
                    (Domain => EW_Pred,
                     Left   => +Check,
                     Right  =>
                       New_Relation
                         (Domain  => EW_Pred,
                          Op_Type => EW_Int,
                          Op      => EW_Eq,
                          Left    => +Input_Length,
                          Right   => +Expected_Length));
               end;
            end loop;
            T :=
              Sequence
                (New_Located_Assert (Stmt, Check, VC_Length_Check),
                 +Tmp);
            T := +Binding_For_Temp (Ada_Node => Empty,
                                   Domain   => EW_Prog,
                                   Tmp      => Lval,
                                   Context  => +T);
         end;
      else
         T := +Tmp;
      end if;
      T :=
        +Insert_Simple_Conversion
        (Domain => EW_Prog,
         To     => Exp_Entity,
         Expr   => +T);
      T := +Binding_For_Temp (Empty, EW_Prog, Tmp, +T);
      return
        Gnat2Why.Expr.New_Assignment
          (Ada_Node => Stmt,
           Lvalue   => Lvalue,
           Expr     => T);
   end Transform_Assignment_Statement;

   -----------------------------
   -- Transform_Attribute_Old --
   -----------------------------

   function Transform_Attribute_Old
     (Expr   : Node_Id;
      Domain : EW_Domain;
      Params : Transformation_Params) return W_Expr_Id
   is
   begin
      --  Expressions that cannot be translated to predicates directly are
      --  translated to (boolean) terms, and compared to "True"

      if Domain = EW_Pred then
         return New_Relation
           (Ada_Node => Expr,
            Domain   => EW_Pred,
            Op_Type  => EW_Bool,
            Left     => +Transform_Attribute_Old (Expr, EW_Term, Params),
            Right    => +True_Term,
            Op       => EW_Eq);
      elsif Params.Phase in Generate_VCs then
         return +Name_For_Old (Expr);
      else
         return New_Old (Expr   => Transform_Expr (Expr, Domain, Params),
                         Domain => Domain);
      end if;
   end Transform_Attribute_Old;

   --------------------
   -- Transform_Attr --
   --------------------

   function Transform_Attr
     (Expr               : Node_Id;
      Domain             : EW_Domain;
      Params             : Transformation_Params) return W_Expr_Id
   is
      Aname   : constant Name_Id := Attribute_Name (Expr);
      Attr_Id : constant Attribute_Id := Get_Attribute_Id (Aname);
      Var     : constant Node_Id      := Prefix (Expr);
      T       : W_Expr_Id;
   begin
      --  The attributes supported here must be a subset
      --  of those supported by a language as a whole.
      --  This case statement must therefore maintain that relationship
      --  with that in SPARK_Definition.Mark_Attribute_Reference
      case Attr_Id is
         when Attribute_Result =>
            if Params.Phase in Generate_VCs | Generate_For_Body then
               T :=
                 New_Deref
                   (Ada_Node => Expr,
                    Right    => Name_For_Result,
                    Typ      => Get_Type (+Name_For_Result));
            else
               T := +New_Result_Ident (EW_Abstract (Etype (Var)));
            end if;

         when Attribute_Old =>
            T := Transform_Attribute_Old (Var, Domain, Params);

         when Attribute_Pred | Attribute_Succ =>
            declare
               Op     : constant EW_Binary_Op :=
                          (if Attr_Id = Attribute_Succ then
                             EW_Add
                           else
                             EW_Substract);
               Old    : W_Expr_Id;
               Offset : W_Expr_Id;
               A_Type : constant Entity_Id := Etype (Var);
               W_Type : EW_Scalar;
            begin
               case Ekind (Etype (Var)) is
                  when Discrete_Kind =>
                     if Is_Standard_Boolean_Type (A_Type) then
                        W_Type := EW_Bool;
                        Ada.Text_IO.Put_Line
                          ("[Transform_Attr] boolean"
                           & Attribute_Id'Image (Attr_Id));
                        raise Not_Implemented;
                     else
                        W_Type := EW_Int;
                        Offset := New_Integer_Constant (Value => Uint_1);
                     end if;

                  when Float_Kind =>
                     W_Type := EW_Real;

                     --  ??? This is not strictly correct; F'Succ (A) is
                     --  usually different from A + F'Succ (0.0). But the
                     --  correct computation will be much more complicated;
                     --  and, as we map floating points to reals, our model
                     --  is quite loose anyway.

                     Offset :=
                       New_Real_Constant
                         (Value =>
                            Eval_Fat.Succ
                              (Root_Type (A_Type),
                               Ureal_0));

                  when Fixed_Point_Kind =>
                     W_Type := EW_Real;
                     Offset :=
                       New_Real_Constant (Value => Small_Value (A_Type));

                  when others =>
                     --  All possible cases should have been handled
                     --  before this point.
                     pragma Assert (False);
                     null;
               end case;

               Old :=
                 Transform_Expr
                   (First (Expressions (Expr)),
                    Why_Types (W_Type),
                    Domain,
                    Params);

               T :=
                 New_Binary_Op
                   (Ada_Node => Expr,
                    Left     => Old,
                    Right    => Offset,
                    Op       => Op,
                    Op_Type  => W_Type);
            end;

         when Attribute_Pos =>
            T := Transform_Expr (First (Expressions (Expr)),
                                 EW_Int_Type,
                                 Domain,
                                 Params);

         when Attribute_Val =>
            declare
               Val_Type : constant W_Type_Id :=
                 Type_Of_Node (Base_Type (Entity (Var)));
            begin
               T := Transform_Expr (First (Expressions (Expr)),
                                    Val_Type,
                                    Domain,
                                    Params);
            end;

         when Attribute_First | Attribute_Last | Attribute_Length =>
            declare
               Ty_Ent : constant Entity_Id :=
                 Unique_Entity (Etype (Var));
               Dim    : constant Uint :=
                 (if Present (Expressions (Expr)) then
                     Expr_Value (First (Expressions (Expr)))
                  else Uint_1);
            begin
               case Ekind (Ty_Ent) is
                  when Array_Kind =>

                     --  Array_Type'First

                     if Nkind (Var) in N_Identifier | N_Expanded_Name
                       and then Is_Type (Entity (Var))
                     then
                        T := New_Attribute_Expr
                          (Nth_Index_Type (Entity (Var), Dim),
                           Attr_Id);

                     --  Object'First

                     else
                        declare
                           Why_Expr : constant W_Expr_Id :=
                             Transform_Expr (Var, Domain, Params);
                        begin
                           T :=
                             Get_Array_Attr
                               (Domain, Why_Expr, Attr_Id,
                                Positive (UI_To_Int (Dim)));
                           if Domain = EW_Prog then
                              T :=
                                +Sequence (New_Ignore (Prog => +Why_Expr), +T);
                           end if;
                        end;
                     end if;

                  when Discrete_Kind | Real_Kind =>
                     T := New_Attribute_Expr (Etype (Var), Attr_Id);

                  when others =>

                     --  All possible cases should have been handled
                     --  before this point.

                     pragma Assert (False);
                     null;
               end case;
            end;

         when Attribute_Loop_Entry =>
            Loop_Entry : declare
               Arg     : constant Node_Id := First (Expressions (Expr));
               Loop_Id : Entity_Id;

            begin
               --  The loop to which attribute Loop_Entry applies is either
               --  identified explicitly in argument, or, if Loop_Entry takes
               --  no arguments, it is the innermost enclosing loop.

               if Present (Arg) then
                  Loop_Id := Entity (Arg);
               else
                  Loop_Id :=
                    Entity (Identifier (Innermost_Enclosing_Loop (Expr)));
               end if;

               pragma Assert (Domain /= EW_Pred
                               and then Params.Phase in Generate_VCs);

               T := +Name_For_Loop_Entry (Var, Loop_Id);
            end Loop_Entry;

         when Attribute_Modulus =>
            T := New_Attribute_Expr (Etype (Var), Attr_Id);

         when Attribute_Mod =>
            T :=
              New_Call (Ada_Node => Expr,
                        Domain   => Domain,
                        Name     => Integer_Mod,
                        Args     =>
                          (1 => Transform_Expr (First (Expressions (Expr)),
                                                EW_Int_Type,
                                                Domain,
                                                Params),
                           2 =>
                           New_Attribute_Expr
                             (Etype (Var), Attribute_Modulus)),
                        Typ   => EW_Int_Type);

         when Attribute_Image =>

            --  We generate the expression String.to_string (image_func (expr))

            T := New_Call (Ada_Node => Expr,
                           Domain   => Domain,
                           Name     => +New_Attribute_Expr
                             (Etype (Var), Attr_Id),
                           Args     =>
                             (1 => Transform_Expr (First (Expressions (Expr)),
                                                   Base_Why_Type (Var),
                                                   Domain,
                              Params)));
            T := New_Call (Ada_Node => Expr,
                           Domain   => Domain,
                           Name     =>
                           Prefix
                             (Ada_Node => Standard_String,
                              M        => E_Module (Standard_String),
                              W        => WNE_To_String),
                           Args     => (1 => T),
                           Typ      => EW_Abstract (Standard_String));

         when Attribute_Value =>
            declare
               Why_Str : constant W_Type_Id :=
                           EW_Abstract (Standard_String);
               Arg     : constant W_Expr_Id :=
                           Transform_Expr (First (Expressions (Expr)),
                                           Why_Str,
                                           Domain,
                                           Params);
               Func    : constant W_Identifier_Id :=
                           +New_Attribute_Expr (Etype (Var), Attr_Id);
            begin
               T :=
                 New_Call
                   (Ada_Node => Expr,
                    Domain   => Domain,
                    Name     =>
                      Prefix
                        (Ada_Node => Standard_String,
                         M        => E_Module (Standard_String),
                         W        => WNE_Of_String),
                    Args     => (1 => Arg));
               if Domain = EW_Prog then
                  T := New_VC_Call
                    (Ada_Node => Expr,
                     Domain   => Domain,
                     Name     => To_Program_Space (Func),
                     Progs    => (1 => T),
                     Reason   => VC_Precondition,
                     Typ      => Base_Why_Type (Var));
               else
                  T := New_Call
                    (Ada_Node => Expr,
                     Domain   => Domain,
                     Name     => Func,
                     Args     => (1 => T),
                     Typ      => Base_Why_Type (Var));
               end if;
            end;

         when Attribute_Update =>
            declare
               Pref        : constant Node_Id := Prefix (Expr);
               Pref_Typ    : constant Entity_Id := Etype (Pref);
               Aggr        : constant Node_Id := First (Expressions (Expr));
               Prefix_Expr : W_Expr_Id;

            begin
               if Is_Record_Type (Pref_Typ) then
                  Prefix_Expr := +Transform_Expr (Domain => Domain,
                                                  Expr   => Pref,
                                                  Params => Params);
                  T := New_Record_Update
                         (Name     => +Prefix_Expr,
                          Updates  =>
                            Transform_Record_Component_Associations
                              (Domain              => Domain,
                               Typ                 => Pref_Typ,
                               Assocs              =>
                                 Component_Associations (Aggr),
                               Params              => Params,
                               In_Attribute_Update => True),
                          Typ      => EW_Abstract (Pref_Typ));

               else
                  pragma Assert (Is_Array_Type (Pref_Typ));

                  if 1 < Number_Dimensions (Pref_Typ) then
                     Ada.Text_IO.Put_Line
                       ("[Transform_Attr] multi-dimensional "
                          & Attribute_Id'Image (Attr_Id));
                     raise Not_Implemented;
                  else
                     T := Transform_Aggregate
                            (Params              => Params,
                             Domain              => Domain,
                             Expr                => Aggr,
                             In_Attribute_Update => True);
                  end if;
               end if;
            end;

         when Attribute_Ceiling    |
              Attribute_Floor      |
              Attribute_Rounding   |
              Attribute_Truncation =>
            declare
               Arg  : constant W_Expr_Id :=
                        Transform_Expr (First (Expressions (Expr)),
                                        EW_Real_Type,
                                        Domain,
                                        Params);
               Func : constant W_Identifier_Id :=
                             (if Attr_Id = Attribute_Ceiling then
                                 Floating_Ceil
                              elsif Attr_Id = Attribute_Floor then
                                 Floating_Floor
                              elsif Attr_Id = Attribute_Rounding then
                                Floating_Round
                              else Floating_Truncate);
            begin
               T := New_Call (Ada_Node => Expr,
                              Domain   => Domain,
                              Name     => Func,
                              Args     => (1 => Arg),
                              Typ      => EW_Int_Type);
            end;

         when Attribute_Min | Attribute_Max =>
            declare
               Ada_Ty : constant Entity_Id := Etype (Expr);
               Base : constant W_Type_Id := Base_Why_Type (Ada_Ty);
               Arg1 : constant W_Expr_Id :=
                 Transform_Expr (First (Expressions (Expr)),
                                 Base,
                                 Domain,
                                 Params);
               Arg2 : constant W_Expr_Id :=
                 Transform_Expr (Next (First (Expressions (Expr))),
                                 Base,
                                 Domain,
                                 Params);
               Func : constant W_Identifier_Id :=
                 (if Is_Discrete_Type (Ada_Ty) then
                      (if Attr_Id = Attribute_Min then Integer_Min
                       else Integer_Max)
                  else (if Attr_Id = Attribute_Min then Floating_Min
                        else Floating_Max));
            begin
               T := New_Call (Ada_Node => Expr,
                              Domain   => Domain,
                              Name     => Func,
                              Args     => (1 => Arg1, 2 => Arg2),
                              Typ      => Base);
            end;

         --  Currently support attribute Valid by assuming it always evaluates
         --  to True.

         when Attribute_Valid =>
            if Domain = EW_Prog then
               declare
                  Why_Expr : constant W_Expr_Id :=
                    Transform_Expr (Var, Domain, Params);
               begin
                  T := +Sequence (New_Ignore (Prog => +Why_Expr), +True_Term);
               end;
            else
               T := +True_Term;
            end if;

         when others =>
            Ada.Text_IO.Put_Line ("[Transform_Attr] id ="
                                  & Attribute_Id'Image (Attr_Id));
            raise Not_Implemented;
      end case;
      return T;
   end Transform_Attr;

   ---------------------
   -- Transform_Binop --
   ---------------------

   function Transform_Binop (Op : N_Binary_Op) return EW_Binary_Op is
   begin
      case Op is
         when N_Op_Add      => return EW_Add;
         when N_Op_Subtract => return EW_Substract;
         when N_Op_Divide   => return EW_Divide;
         when N_Op_Multiply => return EW_Multiply;
         when N_Op_Concat | N_Op_Expon => raise Program_Error;
         when others => raise Program_Error;
      end case;
   end Transform_Binop;

   -------------------------------
   -- Transform_Block_Statement --
   -------------------------------

   function Transform_Block_Statement (N : Node_Id) return W_Prog_Id
   is
      Core : constant W_Prog_Id :=
        Transform_Statements_And_Declarations
          (Statements (Handled_Statement_Sequence (N)));
   begin
      if Present (Declarations (N)) then
         return Transform_Declarations_Block (Declarations (N), Core);
      else
         return Core;
      end if;
   end Transform_Block_Statement;

   --------------------------
   -- Transform_Compare_Op --
   --------------------------

   function Transform_Compare_Op (Op : N_Op_Compare) return EW_Relation is
   begin
      case Op is
         when N_Op_Gt => return EW_Gt;
         when N_Op_Lt => return EW_Lt;
         when N_Op_Eq => return EW_Eq;
         when N_Op_Ge => return EW_Ge;
         when N_Op_Le => return EW_Le;
         when N_Op_Ne => return EW_Ne;
      end case;
   end Transform_Compare_Op;

   -----------------------------
   -- Transform_Concatenation --
   -----------------------------

   function Transform_Concatenation
     (Params : Transformation_Params;
      Domain : EW_Domain;
      Expr   : Node_Id) return W_Expr_Id
   is
      Left      : W_Expr_Id :=
        Transform_Expr (Left_Opnd (Expr), Domain, Params);
      Right     : W_Expr_Id :=
        Transform_Expr (Right_Opnd (Expr), Domain, Params);
      Args       : W_Expr_Array (1 .. 6);
      Arg_Ind    : Positive := 1;
      T          : W_Expr_Id;
      First_Expr : W_Expr_Id;
      Low_Type   : Entity_Id;
      One_Term   : constant W_Expr_Id :=
        New_Integer_Constant (Value => Uint_1);
      Exp_Type   : constant Entity_Id :=
        Get_Ada_Node (+EW_Abstract (Etype (Expr)));
      Comp_Type  : constant W_Type_Id :=
        EW_Abstract (Component_Type (Etype (Expr)));

      function Build_Last_Expr return W_Expr_Id;
      --  build the expression that yields the value of the 'Last attribute
      --  of the concatenation. It is simply
      --    first + length of left opnd + length of right_opnd - 1

      ---------------------
      -- Build_Last_Expr --
      ---------------------

      function Build_Last_Expr return W_Expr_Id is
         Left_Length : constant W_Expr_Id :=
           (if Is_Component_Left_Opnd (Expr) then One_Term
            else Get_Array_Attr (Domain, Left, Attribute_Length, 1));
         Right_Length : constant W_Expr_Id :=
           (if Is_Component_Right_Opnd (Expr) then One_Term
            else Get_Array_Attr (Domain, Right, Attribute_Length, 1));
      begin
         return
           New_Int_Substract
             (Domain,
              New_Int_Add
                (Domain,
                 To_Int (Domain, First_Expr),
                 New_Int_Add
                   (Domain,
                    To_Int (Domain, Left_Length),
                    To_Int (Domain, Right_Length))),
              One_Term);
      end Build_Last_Expr;

   --  Start of Transform_Concatenation

   begin

      --  Step 1: introduce temps for left and right

      Left := New_Temp_For_Expr (Left);
      Right := New_Temp_For_Expr (Right);

      --  Step 2: compute the lower bound of the concatenation
      --  See RM 4.5.3(6-7) for the rules. The test here is taken from
      --  Expand_Concatenate in exp_ch4.adb.

      Low_Type := First_Subtype (Root_Type (Base_Type (Etype (Expr))));

      if Is_Static_Array_Type (Low_Type) then
         First_Expr := Get_Array_Attr (Domain, Low_Type, Attribute_First, 1);

      elsif Is_Component_Left_Opnd (Expr) then
         First_Expr :=
           New_Attribute_Expr
             (Nth_Index_Type (Etype (Expr), 1), Attribute_First);

      else
         First_Expr := Get_Array_Attr (Domain, Left, Attribute_First, 1);
      end if;

      --  Step 3: do to the actual concatenation
      --  We prepare the arguments to the concat call. If one of the sides is
      --  a component, need to possibly convert it to the right type (think of
      --  integer literals, need to convert to Standard__Integer)

      if Is_Component_Left_Opnd (Expr) then
         Args (1) :=
           New_Singleton_Call (Domain,
                               Insert_Simple_Conversion (Domain => Domain,
                                                         Expr   => Left,
                                                         To     => Comp_Type),
                               First_Expr);
         Args (2) := First_Expr;
         Args (3) := First_Expr;
         Arg_Ind := 4;
      else
         Add_Array_Arg (Domain, Args, Left, Arg_Ind);
      end if;

      if Is_Component_Right_Opnd (Expr) then
         Args (4) :=
           New_Singleton_Call (Domain,
                               Insert_Simple_Conversion (Domain => Domain,
                                                         Expr   => Right,
                                                         To     => Comp_Type),
                               One_Term);
         Args (5) := One_Term;
         Args (6) := One_Term;
      else
         Add_Array_Arg (Domain, Args, Right, Arg_Ind);
      end if;

      --  We build the call to concat

      T := New_Concat_Call (Domain, Args, EW_Abstract (Etype (Expr)));

      --  Depending on the lower bound of the concat, the object may not be
      --  slided correctly, because the concat operator in Why assumes that
      --  the new low bound is the one of the left opnd. Correct that.

      if not Is_Component_Left_Opnd (Expr)
        and then Is_Static_Array_Type (Low_Type)
      then
         T :=
           New_Call
             (Domain => Domain,
              Name   =>
                Prefix (M => Array_Modules (1),
                        W => WNE_Array_Slide),
              Args   =>
                (1 => T,
                 2 => Get_Array_Attr (Domain, Left, Attribute_First, 1),
                 3 => First_Expr),
              Typ    => EW_Abstract (Etype (Expr)));
      end if;

      --  Now the expression T is of the Why array type. We need to convert it
      --  to the type of the concatenation expression. Whenever this type is
      --  constrained, we are done. In other cases, we need to convert to the
      --  unconstrained representation. This situation also requires a range
      --  check.

      if not Is_Static_Array_Type (Etype (Expr)) then
         declare
            Target    : constant Entity_Id := Nth_Index_Type (Exp_Type, 1);
            Last_Expr : W_Expr_Id := Build_Last_Expr;
         begin
            if Domain = EW_Prog then
               Last_Expr :=
                 +Do_Range_Or_Index_Check (Ada_Node   => Expr,
                                           Ty         => Target,
                                           W_Expr     => Last_Expr,
                                           Check_Kind => RCK_Range);
            end if;
            T := Array_Convert_From_Base (Domain => Domain,
                                          Target => Exp_Type,
                                          Ar     => T,
                                          First  => First_Expr,
                                          Last   => Last_Expr);

         end;
      end if;

      --  Step 3: bind the introduced names if any, and return

      T := Binding_For_Temp (Domain  => Domain,
                             Tmp     => Left,
                             Context => T);
      T :=  Binding_For_Temp (Domain  => Domain,
                             Tmp     => Right,
                             Context => T);
      return T;
   end Transform_Concatenation;

   ---------------------------
   -- Transform_Declaration --
   ---------------------------

   function Transform_Declaration (Decl : Node_Id) return W_Prog_Id is

      function Get_Base_Type (N : Node_Id) return Entity_Id;
      --  Return the base type when N is the node of a (sub-)type
      --  declaration which requires a check.
      --  Return Empty otherwise.

      -------------------
      -- Get_Base_Type --
      -------------------

      function Get_Base_Type (N : Node_Id) return Entity_Id
      is
         Ent : constant Entity_Id := Defining_Identifier (N);
      begin

         --  Full type declarations can only require checks when they are
         --  scalar types, and then only when the range is non-static.
         if Nkind (N) = N_Full_Type_Declaration then
            if Ekind (Ent) in Scalar_Kind then
               if Is_Static_Range (Get_Range (Ent)) then
                  return Empty;
               end if;
            end if;
            declare
               T_Def : constant Node_Id := Type_Definition (N);
            begin
               case Nkind (T_Def) is
                  when N_Subtype_Indication =>
                     return Entity (Subtype_Mark (T_Def));

                  when N_Derived_Type_Definition =>
                     declare
                        S : constant Node_Id := Subtype_Indication (T_Def);
                     begin
                        if Nkind (S) = N_Subtype_Indication then
                           return Entity (Subtype_Mark (S));
                        else
                           return Entity (S);
                        end if;
                     end;

                  when others =>
                     return Empty;

               end case;
            end;
         else
            declare
               S : constant Node_Id := Subtype_Indication (N);
            begin
               if Nkind (S) = N_Subtype_Indication then
                  return Entity (Subtype_Mark (S));
               else
                  return Entity (S);
               end if;
            end;
         end if;
      end Get_Base_Type;

      R : W_Prog_Id := New_Void;

   --  Start of Transform_Declaration

   begin
      case Nkind (Decl) is
         when N_Object_Declaration =>
            R := Assignment_Of_Obj_Decl (Decl);

         when N_Subtype_Declaration | N_Full_Type_Declaration =>
            declare
               Ent  : constant Entity_Id := Unique_Defining_Entity (Decl);
               Base : Entity_Id := Get_Base_Type (Decl);
            begin
               if Present (Base) then
                  Base := MUT (Base);
               end if;

               case Ekind (Ent) is
                  when Scalar_Kind =>
                     R := Assume_Of_Scalar_Subtype
                            (Params   => Body_Params,
                             N        => Ent,
                             Base     => Base,
                             Do_Check => True);

                  when Array_Kind =>
                     declare
                        Index      : Node_Id;
                        Index_Base : Entity_Id;
                     begin
                        --  For each discrete_subtype_definition that is a
                        --  non-static subtype_indication, we generate a check
                        --  that the range_constraint is compatible with the
                        --  subtype.

                        Index := First_Index (Ent);
                        while Present (Index) loop
                           if Nkind (Index) = N_Subtype_Indication then
                              R := Sequence
                                     (Assume_Of_Subtype_Indication
                                       (Params   => Body_Params,
                                        N        => Index,
                                        Sub_Type => Etype (Index),
                                        Do_Check => Comes_From_Source (Index)),
                                      R);
                           end if;
                           Next (Index);
                        end loop;

                        --  For each range_constraint of an array subtype, we
                        --  generate a check that it is compatible with the
                        --  subtype of the corresponding index in the base
                        --  array type.

                        if Present (Base) then
                           Index := First_Index (Ent);
                           Index_Base := First_Index (Base);
                           while Present (Index) loop
                              R := Sequence
                                     (Assume_Of_Scalar_Subtype
                                       (Params   => Body_Params,
                                        N        => Etype (Index),
                                        Base     => Etype (Index_Base),
                                        Do_Check => Comes_From_Source (Index)),
                                      R);
                              Next (Index);
                              Next (Index_Base);
                           end loop;
                        end if;
                     end;

                  when E_Record_Type | E_Record_Subtype =>
                     declare
                        Comp : Node_Id := First_Component (Ent);
                        Typ  : Node_Id;
                     begin
                        --  For each component_definition that is a non-static
                        --  subtype_indication, we generate a check that the
                        --  range_constraint is compatible with the subtype. It
                        --  is not necessary to do that check on discriminants,
                        --  as the type of discriminants are directly
                        --  subtype_marks, not subtype_indications.

                        while Present (Comp) loop
                           Typ := Subtype_Indication
                                    (Component_Definition (Parent (Comp)));

                           if Present (Typ)
                             and then Nkind (Typ) = N_Subtype_Indication
                           then
                              R := Sequence
                                     (Assume_Of_Subtype_Indication
                                        (Params   => Body_Params,
                                         N        => Typ,
                                         Sub_Type => Etype (Comp),
                                         Do_Check => Comes_From_Source (Typ)),
                                      R);
                           end if;
                           Next_Component (Comp);
                        end loop;
                     end;

                  when Private_Kind =>
                     null;

                  when others =>
                     Ada.Text_IO.Put_Line
                       ("[Transform_Declaration] ekind ="
                        & Entity_Kind'Image (Ekind (Ent)));
                     raise Not_Implemented;
               end case;
            end;

         when N_Pragma =>
            R := Transform_Pragma (Decl);

         when N_Raise_xxx_Error | N_Raise_Statement =>
            R := Transform_Raise (Decl);

         when others =>
            null;
      end case;
      return R;
   end Transform_Declaration;

   ----------------------------------
   -- Transform_Declarations_Block --
   ----------------------------------

   function Transform_Declarations_Block (L : List_Id; Core : W_Prog_Id)
      return W_Prog_Id
   is
      Cur_Decl : Node_Id := Last (L);
      R        : W_Prog_Id := Core;
   begin
      while Present (Cur_Decl) loop
         R := Sequence (Transform_Declaration (Cur_Decl), R);
         Prev (Cur_Decl);
      end loop;
      return R;
   end Transform_Declarations_Block;

   ----------------------------------------
   -- Transform_Declarations_From_Source --
   ----------------------------------------

   function Transform_Declarations_From_Source
     (L : List_Id) return W_Prog_Id
   is
      Cur_Decl : Node_Id := First (L);
      Result   : W_Prog_Id := New_Void;
   begin
      while Present (Cur_Decl) and then not Comes_From_Source (Cur_Decl) loop
         Next (Cur_Decl);
      end loop;
      while Present (Cur_Decl) loop
         Result := Sequence (Result, Transform_Declaration (Cur_Decl));
         Next (Cur_Decl);
      end loop;
      return Result;
   end Transform_Declarations_From_Source;

   --------------------------------------------
   -- Transform_Declarations_Not_From_Source --
   --------------------------------------------

   function Transform_Declarations_Not_From_Source
     (L : List_Id) return W_Prog_Id
   is
      Cur_Decl : Node_Id := First (L);
      Result   : W_Prog_Id := New_Void;
   begin
      while Present (Cur_Decl) and then not Comes_From_Source (Cur_Decl) loop
         Result := Sequence (Result, Transform_Declaration (Cur_Decl));
         Next (Cur_Decl);
      end loop;
      return Result;
   end Transform_Declarations_Not_From_Source;

   -------------------------------
   -- Transform_Discrete_Choice --
   -------------------------------

   function Transform_Discrete_Choice
     (Choice      : Node_Id;
      Choice_Type : Entity_Id;
      Expr        : W_Expr_Id;
      Domain      : EW_Domain;
      Params      : Transformation_Params) return W_Expr_Id
   is
      Subdomain : constant EW_Domain :=
                    (if Domain = EW_Pred then EW_Term else Domain);
      Is_Range  : constant Boolean := Discrete_Choice_Is_Range (Choice);

      R : W_Expr_Id;
   begin
      if Nkind (Choice) = N_Others_Choice then
         R := New_Literal (Domain => Domain, Value => EW_True);

      elsif Is_Range then
         R := Range_Expr (Choice, Expr, Domain, Params, EW_Int_Type);

         --  In programs, we generate a check that the range_constraint of a
         --  subtype_indication is compatible with the given subtype.

         if Domain = EW_Prog
           and then Nkind (Choice) = N_Subtype_Indication
         then
            R := +Sequence
                   (Assume_Of_Subtype_Indication (Params   => Params,
                                                  N        => Choice,
                                                  Sub_Type => Choice_Type,
                                                  Do_Check => True),
                    +R);
         end if;

      else
         R := New_Comparison
           (Cmp       => EW_Eq,
            Left      => Expr,
            Right     => Transform_Expr (Expr          => Choice,
                                         Expected_Type => EW_Int_Type,
                                         Domain        => Subdomain,
                                         Params        => Params),
            Domain    => Domain);

         --  In programs, we generate a check that the non-static value of a
         --  choice belongs to the given subtype.

         if Domain = EW_Prog
           and then not Is_OK_Static_Expression (Choice)
         then
            R := +Sequence
                   (+New_Ignore (Prog =>
                      Do_Range_Or_Index_Check
                        (Ada_Node   => Choice,
                         Ty         => Choice_Type,
                         W_Expr     =>
                           Transform_Expr (Expr          => Choice,
                                           Expected_Type => EW_Int_Type,
                                           Domain        => Subdomain,
                                           Params        => Params),
                         Check_Kind => RCK_Range)),
                    +R);
         end if;
      end if;

      return R;
   end Transform_Discrete_Choice;

   --------------------------------
   -- Transform_Discrete_Choices --
   --------------------------------

   function Transform_Discrete_Choices
     (Choices      : List_Id;
      Choice_Type  : Entity_Id;
      Matched_Expr : W_Expr_Id;
      Cond_Domain  : EW_Domain;
      Params       : Transformation_Params) return W_Expr_Id
   is
      Cur_Choice : Node_Id   := First (Choices);
      C          : W_Expr_Id := New_Literal (Domain => Cond_Domain,
                                             Value  => EW_False);
   begin
      while Present (Cur_Choice) loop
         C := New_Or_Else_Expr
           (C,
            Transform_Discrete_Choice (Choice      => Cur_Choice,
                                       Choice_Type => Choice_Type,
                                       Expr        => Matched_Expr,
                                       Domain      => Cond_Domain,
                                       Params      => Params),
            Cond_Domain);
         Next (Cur_Choice);
      end loop;
      return C;
   end Transform_Discrete_Choices;

   ----------------------------
   -- Transform_Enum_Literal --
   ----------------------------

   function Transform_Enum_Literal
     (Expr         : Node_Id;
      Enum         : Entity_Id;
      Domain       : EW_Domain)
      return W_Expr_Id is
   begin
      --  Deal with special cases: True/False for boolean literals

      if Enum = Standard_True then
         return New_Literal (Value => EW_True,
                             Domain => Domain,
                             Ada_Node => Standard_Boolean);
      end if;

      if Enum = Standard_False then
         return New_Literal (Value => EW_False,
                             Domain => Domain,
                             Ada_Node => Standard_Boolean);
      end if;

      --  all other enumeration literals are expressed by integers

      return New_Integer_Constant
               (Ada_Node => Expr,
                Value    => Enumeration_Pos (Enum));
   end Transform_Enum_Literal;

   --------------------
   -- Transform_Expr --
   --------------------

   function Transform_Expr
     (Expr          : Node_Id;
      Expected_Type : W_Type_Id;
      Domain        : EW_Domain;
      Params        : Transformation_Params) return W_Expr_Id
   is

      --  The multiplication and division operations on fixed-point types have
      --  a return type of universal_fixed (with no bounds), which is used as
      --  an overload resolution trick to allow free conversion between certain
      --  real types on the result of multiplication or division. The target
      --  non-universal type determines the actual sort of multiplication
      --  or division performed, and therefore determines the possibility of
      --  overflow. In the compiler, the multiplication is expanded so the
      --  operands are first converted to some common type, so back ends don't
      --  see the universal_fixed Etype. Here, we are seeing the unexpanded
      --  operation because we are running in a mode that disables the
      --  expansion. Hence, we recognize the universal_fixed case specially
      --  and in that case use the target type of the enclosing conversion.

      Expr_Type : constant Entity_Id :=
        (if Nkind_In (Expr, N_Op_Multiply, N_Op_Divide)
           and then Etype (Expr) = Universal_Fixed
           and then Nkind (Parent (Expr)) = N_Type_Conversion
         then
            Etype (Parent (Expr))
         else
            Etype (Expr));

      T            : W_Expr_Id;
      Pretty_Label : Name_Id := No_Name;
      Local_Params : Transformation_Params := Params;

   begin
      --  We check whether we need to generate a pretty printing label. If we
      --  do, we set the corresponding flag to "False" so that the label is not
      --  printed for subterms.

      if Domain = EW_Pred
        and then Local_Params.Gen_Image
        and then Is_Pretty_Node (Expr)
      then
         Pretty_Label := New_Pretty_Label (Expr);
         Local_Params.Gen_Image := False;
      end if;

      --  Expressions that cannot be translated to predicates directly are
      --  translated to (boolean) terms, and compared to "True"

      if Domain = EW_Pred and then
         not (Nkind (Expr) in N_Op_Compare | N_Op_Not | N_Op_And | N_And_Then
         | N_Op_Or | N_Or_Else | N_In | N_If_Expression |
         N_Quantified_Expression | N_Case_Expression) and then
         not (Nkind (Expr) in N_Identifier | N_Expanded_Name and then
              Ekind (Entity (Expr)) in E_Enumeration_Literal and then
              (Entity (Expr) = Standard_True or else
               Entity (Expr) = Standard_False))
      then
         T :=
           New_Relation
             (Ada_Node => Expr,
              Domain   => EW_Pred,
              Op_Type  => EW_Bool,
              Left     =>
              +Transform_Expr (Expr, EW_Bool_Type, EW_Term, Local_Params),
              Right    => +True_Prog,
              Op       => EW_Eq);
      elsif Domain /= EW_Pred and then
        Is_Discrete_Type (Expr_Type) and then
        Compile_Time_Known_Value (Expr)
      then

         --  Optimization: if we have a discrete value that is statically
         --  known, use the static value.

         T :=
           New_Integer_Constant (Ada_Node => Expr,
                                 Value    => Expr_Value (Expr));
      else
         case Nkind (Expr) is
         when N_Aggregate =>
            declare
               Expr_Type : constant Entity_Id := Type_Of_Node (Expr);
            begin
               if Is_Record_Type (Expr_Type) then
                  pragma Assert (Is_Empty_List (Expressions (Expr)));
                  T :=
                    New_Record_Aggregate
                      (Associations =>
                         Transform_Record_Component_Associations
                           (Domain,
                            Expr_Type,
                            Component_Associations (Expr),
                            Local_Params),
                       Typ => EW_Abstract (Expr_Type));
               else
                  pragma Assert
                    (Is_Array_Type (Expr_Type) or else
                     Is_String_Type (Expr_Type));

                  T := Transform_Aggregate (Params => Local_Params,
                                            Domain => Domain,
                                            Expr   => Expr);
               end if;
            end;

         when N_Slice =>
            T := Transform_Slice (Local_Params, Domain, Expr);

         when N_Integer_Literal =>
            T :=
              New_Integer_Constant
                (Ada_Node => Expr,
                 Value    => Intval (Expr));

         --  Note: although the original node for a real literal might be
         --  closer to the source code expression of the value, this original
         --  node should not be used for transforming the node into Why.
         --  Indeed, a source float literal in Ada might not be representable
         --  in machine, in which case the frontend rewrites the value into a
         --  machine representable value (respecting the Ada RM rules, so
         --  getting the closest representable floating-point value).

         --  The procedure printing this node in Why takes care of putting the
         --  value in a suitable form for provers. In particular, we want to
         --  avoid printing divisions between real numbers, which provers don't
         --  handle well, even when the division can be expressed exactly as a
         --  decimal number.

         when N_Real_Literal =>
            T := New_Real_Constant (Ada_Node => Expr,
                                    Value    => Realval (Expr));

         when N_Character_Literal =>

            T :=
              New_Integer_Constant (Ada_Node => Expr,
                                    Value    => Char_Literal_Value (Expr));

         --  Deal with identifiers:
         --  * Enumeration literals: deal with special cases True and
         --    False, otherwise such literals are just constants
         --  * local variables are always references
         --  * global constants are logics in Why
         --  * global mutable variables are references
         --  * loop parameters are always mutable, and of type int

         when N_String_Literal =>
            declare
               M : W_Module_Id := E_Module (Expr);
               Id : W_Identifier_Id;
            begin
               if M = Why_Empty then
                  Transform_String_Literal (Local_Params, Expr);
                  M := E_Module (Expr);
               end if;
               Id :=
                 New_Identifier
                   (Ada_Node => Expr,
                    Domain   => Domain,
                    Module   => M,
                    Symbol   => Get_Name (M),
                    Typ      => New_Abstract_Base_Type (Type_Of_Node (Expr)));
               T := +Id;
            end;

         when N_Identifier | N_Expanded_Name =>
            T := Transform_Identifier (Local_Params, Expr,
                                       Entity (Expr),
                                       Domain);

         when N_Op_Compare =>

            --  special case for equality between Booleans in predicates

            if Domain = EW_Pred and then
              Nkind (Expr) = N_Op_Eq and then
              Is_Standard_Boolean_Type (Etype (Left_Opnd (Expr)))
            then
               T :=
                 New_Connection
                   (Domain => EW_Pred,
                    Left   =>
                      Transform_Expr
                        (Left_Opnd (Expr),
                         EW_Bool_Type,
                         EW_Pred,
                         Local_Params),
                    Right  =>
                      Transform_Expr
                        (Right_Opnd (Expr),
                         EW_Bool_Type,
                         EW_Pred,
                         Local_Params),
                    Op     => EW_Equivalent);

            elsif Is_Array_Type (Etype (Left_Opnd (Expr)))
              and then Nkind (Expr) in N_Op_Eq | N_Op_Ne
            then
               T := Transform_Array_Equality (Local_Params, Expr, Domain);
            elsif Is_Array_Type (Etype (Left_Opnd (Expr))) then
               T := Transform_Array_Comparison (Local_Params, Expr, Domain);
            else
               declare
                  Left  : constant Node_Id := Left_Opnd (Expr);
                  Right : constant Node_Id := Right_Opnd (Expr);

                  BT        : constant W_Type_Id :=
                    Base_Why_Type (Left, Right);
                  Subdomain : constant EW_Domain :=
                    (if Domain = EW_Pred then EW_Term else Domain);
                  Left_Arg  : constant W_Expr_Id :=
                    Transform_Expr (Left, BT, Subdomain,
                                    Local_Params);
                  Right_Arg : constant W_Expr_Id :=
                    Transform_Expr (Right, BT, Subdomain,
                                    Local_Params);

               begin
                  if Is_Record_Type (Etype (Left)) then
                     pragma Assert (Root_Record_Type (Etype (Left)) =
                                      Root_Record_Type (Etype (Right)));
                     pragma Assert (Root_Record_Type (Etype (Left)) =
                                      Get_Ada_Node (+BT));
                     T :=
                       New_Call
                         (Ada_Node => Expr,
                          Domain   => Subdomain,
                          Name     =>
                            Prefix (Ada_Node => Get_Ada_Node (+BT),
                                    M        => E_Module (Get_Ada_Node (+BT)),
                                    W        => WNE_Bool_Eq),
                          Args     => (1 => Left_Arg,
                                       2 => Right_Arg),
                          Typ      => EW_Bool_Type);

                     if Domain = EW_Pred then
                        T := New_Comparison
                          (Cmp       => Transform_Compare_Op (Nkind (Expr)),
                           Left      => T,
                           Right     => New_Literal (Domain => Subdomain,
                                                     Value  => EW_True),
                           Domain    => Domain);

                     elsif Nkind (Expr) = N_Op_Ne then
                        T :=
                          New_Call (Domain => Domain,
                                    Name   => To_Ident (WNE_Bool_Not),
                                    Args   => (1 => T),
                                    Typ    => EW_Bool_Type);
                     end if;
                  else
                     T := New_Comparison
                       (Cmp       => Transform_Compare_Op (Nkind (Expr)),
                        Left      => Left_Arg,
                        Right     => Right_Arg,
                        Domain    => Domain);
                  end if;
               end;
            end if;

         when N_Op_Minus =>
            --  unary minus
            declare
               Right : constant Node_Id := Right_Opnd (Expr);
            begin
               T :=
                 New_Unary_Op
                   (Ada_Node => Expr,
                    Op       => EW_Minus,
                    Right    =>
                    +Transform_Expr (Right, Base_Why_Type (Right), Domain,
                     Local_Params),
                    Op_Type  => Get_Base_Type (Base_Why_Type (Right)));
               T := Apply_Modulus_Or_Rounding (Expr_Type, T, Domain);
            end;

         when N_Op_Plus =>

            --  unary plus

            declare
               Right : constant Node_Id := Right_Opnd (Expr);
            begin
               T := Transform_Expr
                 (Right,
                  Base_Why_Type (Right),
                  Domain,
                  Local_Params);
            end;

         when N_Op_Abs =>
            declare
               Right : constant Node_Id := Right_Opnd (Expr);
               Typ   : constant W_Type_Id := Base_Why_Type (Right);
            begin
               T :=
                 New_Call
                   (Ada_Node => Expr,
                    Domain   => Domain,
                    Name     =>
                      New_Abs (Get_Base_Type (Typ)),
                    Args     =>
                      (1 => Transform_Expr
                         (Right,
                          Typ,
                          Domain,
                          Local_Params)),
                    Typ     => Typ);
            end;

         when N_Op_Add | N_Op_Multiply | N_Op_Subtract =>
            --  The arguments of arithmetic functions have to be of base
            --  scalar types
            declare
               Left  : constant Node_Id := Left_Opnd (Expr);
               Right : constant Node_Id := Right_Opnd (Expr);
               Base  : constant W_Type_Id := Base_Why_Type (Left, Right);
            begin
               T :=
                 New_Binary_Op
                   (Ada_Node => Expr,
                    Left     => Transform_Expr (Left,
                                                Base,
                                                Domain,
                                                Local_Params),
                    Right    => Transform_Expr (Right,
                                                Base,
                                                Domain,
                                                Local_Params),
                    Op       => Transform_Binop (Nkind (Expr)),
                    Op_Type  => Get_Base_Type (Base));
               T := Apply_Modulus_Or_Rounding (Expr_Type, T, Domain);
            end;

         when N_Op_Divide =>
            declare
               Left  : constant Node_Id := Left_Opnd (Expr);
               Right : constant Node_Id := Right_Opnd (Expr);
               Base  : constant W_Type_Id := Base_Why_Type (Left, Right);
               Name  : W_Identifier_Id;
               L_Why, R_Why : W_Expr_Id;
            begin
               L_Why :=
                 Transform_Expr (Left,
                                 Base,
                                 Domain,
                                 Local_Params);
               R_Why :=
                 Transform_Expr (Right,
                                 Base,
                                 Domain,
                                 Local_Params);
               Name := New_Division (Get_Base_Type (Base));
               if Domain = EW_Prog and then Do_Division_Check (Expr) then
                  T :=
                    New_VC_Call
                      (Ada_Node => Expr,
                       Domain   => Domain,
                       Name     => To_Program_Space (Name),
                       Progs    => (1 => L_Why, 2 => R_Why),
                       Reason   => VC_Division_Check,
                       Typ      => Base);
               else
                  T :=
                    New_Call
                      (Ada_Node => Expr,
                       Domain   => Domain,
                       Name     => Name,
                       Args     => (1 => L_Why, 2 => R_Why),
                       Typ      => Base);
               end if;

               T := Apply_Modulus_Or_Rounding (Expr_Type, T, Domain);
            end;

         when N_Op_Rem | N_Op_Mod =>
            declare
               Left  : constant Node_Id := Left_Opnd (Expr);
               Right : constant Node_Id := Right_Opnd (Expr);
               Base  : constant W_Type_Id := Base_Why_Type (Left, Right);
               Name  : W_Identifier_Id;
            begin
               Name := (if Nkind (Expr) = N_Op_Rem then Integer_Rem
                        else Integer_Mod);
               Name := (if Domain = EW_Prog then
                          To_Program_Space (Name)
                        else
                          Name);
               T :=
                 New_VC_Call
                   (Ada_Node => Expr,
                    Domain   => Domain,
                    Name     => Name,
                    Progs    =>
                      (1 => Transform_Expr (Left,
                                            Base,
                                            Domain,
                                            Local_Params),
                       2 => Transform_Expr (Right,
                                            Base,
                                            Domain,
                                            Local_Params)),
                    Reason   => VC_Division_Check,
                    Typ      => Base);
            end;

         when N_Op_Expon =>
            declare
               Left    : constant Node_Id := Left_Opnd (Expr);
               Right   : constant Node_Id := Right_Opnd (Expr);
               Name    : W_Identifier_Id;
               W_Right : constant W_Expr_Id :=
                 Transform_Expr (Right,
                                 EW_Int_Type,
                                 Domain,
                                 Local_Params);
               Typ     : constant W_Type_Id := Base_Why_Type (Left);
            begin
               Name := New_Exp (Get_Base_Type (Typ));

               T := New_Call
                      (Ada_Node => Expr,
                       Domain   => Domain,
                       Name     => Name,
                       Args     =>
                         (1 => Transform_Expr (Left,
                                               Base_Why_Type (Left),
                                               Domain,
                                               Local_Params),
                          2 => W_Right),
                       Typ      => Typ);

            end;

         when N_Op_Not =>
            if Is_Array_Type (Etype (Right_Opnd (Expr))) then
               T := Transform_Array_Negation (Local_Params, Expr, Domain,
                                              Do_Check => Domain = EW_Prog);
            else
               if Domain = EW_Term then
                  T :=
                    New_Call
                      (Ada_Node => Expr,
                       Domain   => Domain,
                       Name     => New_Identifier (Name => "notb"),
                       Args     =>
                         (1 => Transform_Expr
                            (Right_Opnd (Expr),
                             EW_Bool_Type,
                             Domain,
                             Local_Params)),
                       Typ      => EW_Bool_Type);
               else
                  T :=
                    New_Not
                      (Right  => Transform_Expr (Right_Opnd (Expr),
                       EW_Bool_Type,
                       Domain,
                       Local_Params),
                       Domain => Domain);
               end if;
            end if;

         when N_Op_And | N_Op_Or | N_Op_Xor =>

            if Is_Array_Type (Etype (Left_Opnd (Expr))) then
               T := Transform_Array_Logical_Op (Local_Params, Expr, Domain,
                                                Do_Check => Domain = EW_Prog);
            else
               declare
                  Base  : constant W_Type_Id :=
                    (if Is_Boolean_Type (Expr_Type) then EW_Bool_Type
                     else EW_Int_Type);
                  Left  : constant W_Expr_Id :=
                    Transform_Expr (Left_Opnd (Expr),
                                    Base,
                                    Domain,
                                    Local_Params);
                  Right : constant W_Expr_Id :=
                    Transform_Expr (Right_Opnd (Expr),
                                    Base,
                                    Domain,
                                    Local_Params);
               begin
                  if Nkind (Expr) = N_Op_And then
                     T := New_And_Expr (Left, Right, Domain, Base);
                  elsif Nkind (Expr) = N_Op_Or then
                     T := New_Or_Expr (Left, Right, Domain, Base);
                  else
                     T := New_Xor_Expr (Left, Right, Domain, Base);
                  end if;
               end;
            end if;

         when N_Short_Circuit =>
            Short_Circuit : declare

               function New_Short_Circuit_Expr
                 (Left, Right : W_Expr_Id;
                  Domain      : EW_Domain) return W_Expr_Id;
               --  Dispatch over functions to create a short-circuit Why expr

               ----------------------------
               -- New_Short_Circuit_Expr --
               ----------------------------

               function New_Short_Circuit_Expr
                 (Left, Right : W_Expr_Id;
                  Domain      : EW_Domain) return W_Expr_Id is
               begin
                  if Nkind (Expr) = N_And_Then then
                     return New_And_Then_Expr (Left, Right, Domain);
                  else
                     return New_Or_Else_Expr (Left, Right, Domain);
                  end if;
               end New_Short_Circuit_Expr;

            --  Start of Short_Circuit

            begin
               Ada_Ent_To_Why.Push_Scope (Symbol_Table);
               if Present (Actions (Expr)) then
                  Transform_Actions_Preparation (Actions (Expr));
               end if;

               T :=
                 New_Short_Circuit_Expr
                   (Left   => Transform_Expr (Left_Opnd (Expr),
                                              EW_Bool_Type,
                                              Domain,
                                              Local_Params),
                    Right  => Transform_Expr (Right_Opnd (Expr),
                                              EW_Bool_Type,
                                              Domain,
                                              Local_Params),
                    Domain => Domain);

               if Present (Actions (Expr)) then
                  T := Transform_Actions (Actions (Expr),
                                          T,
                                          Domain,
                                          Local_Params);
               end if;

               Ada_Ent_To_Why.Pop_Scope (Symbol_Table);
            end Short_Circuit;

         when N_Op_Concat =>
            T := Transform_Concatenation (Local_Params, Domain, Expr);

         when N_Membership_Test =>
            T := Transform_Membership_Expression (Local_Params, Domain, Expr);

         when N_Quantified_Expression =>
            T := Transform_Quantified_Expression (Expr, Domain, Local_Params);

         when N_If_Expression =>
            declare
               Cond        : constant Node_Id := First (Expressions (Expr));
               Then_Part   : constant Node_Id := Next (Cond);
               Else_Part   : constant Node_Id := Next (Then_Part);
               Cond_Domain : constant EW_Domain :=
                 (if Domain = EW_Term then EW_Pred else Domain);
               Then_Expr, Else_Expr : W_Expr_Id;
               Condition   : W_Expr_Id;
            begin
               Then_Expr :=
                 Transform_Expr_With_Actions (Then_Part,
                                              Then_Actions (Expr),
                                              Type_Of_Node (Expr_Type),
                                              Domain,
                                              Local_Params);
               Else_Expr :=
                 Transform_Expr_With_Actions (Else_Part,
                                              Else_Actions (Expr),
                                              Type_Of_Node (Expr_Type),
                                              Domain,
                                              Local_Params);
               Local_Params.Gen_Image := False;
               Condition :=
                 +Transform_Expr (Cond,
                                  EW_Bool_Type,
                                  Cond_Domain,
                                  Local_Params);

               T :=
                  New_Conditional
                     (Ada_Node  => Expr,
                      Domain    => Domain,
                      Condition => Condition,
                      Then_Part => Then_Expr,
                      Else_Part => Else_Expr,
                      Typ       => Get_Type (Then_Expr));
            end;

         when N_Qualified_Expression |
              N_Type_Conversion      =>

            --  When converting between discrete types, only require that the
            --  converted expression is translated into a value of the expected
            --  type. Necessary checks and conversions will be introduced at
            --  the end of Transform_Expr below.

            if Domain /= EW_Prog and Ekind (Expr_Type) in Discrete_Kind then
               T := Transform_Expr (Expression (Expr),
                                    Expected_Type,
                                    Domain,
                                    Local_Params);

            --  In other cases, require that the converted expression
            --  is translated into a value of the type of the conversion
            --  Current_Type.

            --  When converting to a flating-point or fixed-point type,
            --  this ensures that a rounding operation can be applied on
            --  the intermediate real value.

            --  When converting to a discriminant record or an array, this
            --  ensures that the proper target type can be retrieved from
            --  the current node, to call the right checking function.

            else
               T := Transform_Expr (Expression (Expr),
                                    Type_Of_Node (Expr),
                                    Domain,
                                    Local_Params);
            end if;

         when N_Unchecked_Type_Conversion =>

            --  Source unchecked type conversion nodes were rewritten as such
            --  by SPARK_Rewrite.Rewrite_Call, keeping the original call to an
            --  instance of Unchecked_Conversion as the Original_Node of the
            --  new N_Unchecked_Type_Conversion node, and marking the node as
            --  coming from source. We translate this original node to Why.

            if Comes_From_Source (Expr) then
               T := Transform_Expr (Original_Node (Expr),
                                    Expected_Type,
                                    Domain,
                                    Local_Params);

            --  Compiler inserted unchecked type conversions should be
            --  transparent for Why with our translation.

            else
               T := Transform_Expr (Expression (Expr),
                                    Expected_Type,
                                    Domain,
                                    Local_Params);
            end if;

         when N_Function_Call =>
            declare
               Subp       : constant Entity_Id := Entity (Name (Expr));
               Why_Name   : constant W_Identifier_Id :=
                 W_Identifier_Id
                   (Transform_Identifier (Params       => Local_Params,
                                          Expr         => Expr,
                                          Ent          => Subp,
                                          Domain       => Domain));
               Nb_Of_Refs : Natural;
               Args       : constant W_Expr_Array :=
                 Compute_Call_Args (Expr, Domain, Nb_Of_Refs, Local_Params);

            begin
               if Why_Subp_Has_Precondition (Subp) then
                  T :=
                    +New_VC_Call
                    (Name     => Why_Name,
                     Progs    => Args,
                     Ada_Node => Expr,
                     Domain   => Domain,
                     Reason   => VC_Precondition,
                     Typ      => Get_Typ (Why_Name));

               else
                  T :=
                    New_Call
                      (Name     => Why_Name,
                       Args     => Args,
                       Ada_Node => Expr,
                       Domain   => Domain,
                       Typ      => Get_Typ (Why_Name));
               end if;

               pragma Assert (Nb_Of_Refs = 0,
                              "Only pure functions are in alfa");
            end;

         when N_Indexed_Component | N_Selected_Component =>
            T := One_Level_Access (Expr,
                                   Transform_Expr
                                     (Prefix (Expr), Domain, Local_Params),
                                   Domain,
                                   Local_Params);

         when N_Attribute_Reference =>
            T := Transform_Attr (Expr, Domain, Local_Params);

         when N_Case_Expression =>
            T := Case_Expr_Of_Ada_Node
                   (Expr,
                    Expected_Type,
                    Domain,
                    Local_Params);

         when N_Expression_With_Actions =>
            if not (Domain = EW_Prog) then
               Ada.Text_IO.Put_Line
                 ("[Transform_Expr] expression with action");
               raise Not_Implemented;
            end if;

            T :=
               +Sequence
                 (Transform_Statements_And_Declarations (Actions (Expr)),
                  +Transform_Expr (Expression (Expr),
                                   Expected_Type,
                                   EW_Prog,
                                   Local_Params));

         when others =>
            Ada.Text_IO.Put_Line ("[Transform_Expr] kind ="
                                  & Node_Kind'Image (Nkind (Expr)));
            raise Not_Implemented;
         end case;
      end if;

      --  We now have the translation of the Ada expression in [T], pending
      --  checks and conversion. We now do the wrapping up to insert all those
      --  if needed.

      --  This label will be used for pretty printing the expression

      if Pretty_Label /= No_Name then
         declare
            Label_Set : Name_Id_Set := Name_Id_Sets.To_Set (Pretty_Label);
         begin
            Label_Set.Include (New_Located_Label (Expr, Is_VC => False));
            T :=
              New_Label (Labels => Label_Set,
                         Def => T,
                         Domain => Domain,
                         Typ    => Get_Type (T));
         end;
      end if;

      --  Insert an overflow check if flag Do_Overflow_Check is set. No
      --  conversion should be needed, as overflow checks are only set on
      --  intermediate expressions, whose transformation into Why should
      --  always have type "int" or "real". We start by checking that Expr has
      --  a kind on which we can call Do_Overflow_Check, otherwise there is
      --  nothing to do.

      --  Note that N_Type_Conversions *may* have a Do_Overflow_Check flag, but
      --  they are actually for range checks and are checked elsewhere. See the
      --  documentation of sinfo.ads.

      if Domain = EW_Prog
        and then Nkind (Expr) in N_Attribute_Reference |
                                 N_Case_Expression     |
                                 N_If_Expression       |
                                 N_Op
        and then Do_Overflow_Check (Expr)
      then
         --  Depending on the current mode for integer overflow checks, the
         --  operation is either done in the base type (Strict mode), or in
         --  Long_Long_Integer (Minimized mode) if needed, or in arbitrary
         --  precision if needed (Eliminated mode). A check may only be
         --  generated in the Strict and Minimized modes, and the type
         --  used for the bounds is the base type in the first case, and
         --  Long_Long_Integer in the second case (which is its own base type).

         if Is_Signed_Integer_Type (Expr_Type) then
            declare
               Mode : Overflow_Mode_Type;
            begin
               case Params.Phase is
                  when Generate_VCs_For_Body =>
                     Mode := Opt.Suppress_Options.Overflow_Mode_General;
                  when Generate_VCs_For_Assertion =>
                     Mode := Opt.Suppress_Options.Overflow_Mode_Assertions;
                  when others =>
                     raise Program_Error;
               end case;

               case Mode is
                  when Strict =>
                     T := Insert_Overflow_Check (Expr, T, Expr_Type);
                  when Minimized =>
                     T := Insert_Overflow_Check (Expr, T, Standard_Integer_64);
                  when Eliminated =>
                     null;
                  when Not_Set =>
                     raise Program_Error;
               end case;
            end;

         --  Not a signed integer type. Always perform the overflow check.

         else
            T := Insert_Overflow_Check (Expr, T, Expr_Type);
         end if;
      end if;

      --  Convert the expression to the expected type, if needed. This is
      --  intertwined with inserting range checks, and Insert_Conversion does
      --  both. This is because range checks need to be done on the Why "int"
      --  type, so they may trigger a conversion, or if a conversion is already
      --  needed, must be done on the "right side" of the conversion.
      --  Note that Insert_Conversion is smart enough to not insert any
      --  conversion when it's not needed.

      --  A range check is needed only in programs (Domain EW_Prog), and on
      --  nodes that have the range check flag. For type conversions, the
      --  Do_Overflow_Check actually means that a range check is needed,
      --  instead of an overflow check (see sinfo.ads and the discussion of
      --  range checks and overflow checks there). Because range checks are
      --  determined by looking at the parent node, in that special case we go
      --  one step down for the Range_Check_Node.

      --  In predicate domain, only the Boolean type is used, no conversion is
      --  needed.

      if Domain in EW_Pred then
         null;
      else
         T := Insert_Checked_Conversion (Ada_Node => Expr,
                                         Ada_Type => Expr_Type,
                                         Domain   => Domain,
                                         Expr     => T,
                                         To       => Expected_Type);
      end if;

      return T;
   end Transform_Expr;

   function Transform_Expr
     (Expr   : Node_Id;
      Domain : EW_Domain;
      Params : Transformation_Params) return W_Expr_Id is
   begin
      return Transform_Expr
        (Expr, Type_Of_Node (Expr), Domain, Params);
   end Transform_Expr;

   ---------------------------------
   -- Transform_Expr_With_Actions --
   ---------------------------------

   function Transform_Expr_With_Actions
     (Expr          : Node_Id;
      Actions       : List_Id;
      Expected_Type : W_Type_Id;
      Domain        : EW_Domain;
      Params        : Transformation_Params) return W_Expr_Id
   is
      T            : W_Expr_Id;

   begin
      Ada_Ent_To_Why.Push_Scope (Symbol_Table);
      if Present (Actions) then
         Transform_Actions_Preparation (Actions);
      end if;

      T := Transform_Expr (Expr,
                           Expected_Type,
                           Domain,
                           Params);

      if Present (Actions) then
         T := Transform_Actions (Actions, T, Domain, Params);
      end if;

      Ada_Ent_To_Why.Pop_Scope (Symbol_Table);
      return T;
   end Transform_Expr_With_Actions;

   function Transform_Expr_With_Actions
     (Expr    : Node_Id;
      Actions : List_Id;
      Domain  : EW_Domain;
      Params  : Transformation_Params) return W_Expr_Id is
   begin
      return Transform_Expr_With_Actions
        (Expr, Actions, Type_Of_Node (Expr), Domain, Params);
   end Transform_Expr_With_Actions;

   --------------------------
   -- Transform_Identifier --
   --------------------------

   function Transform_Identifier
     (Params : Transformation_Params;
      Expr   : Node_Id;
      Ent    : Entity_Id;
      Domain : EW_Domain) return W_Expr_Id
   is
      C   : constant Ada_Ent_To_Why.Cursor :=
        Ada_Ent_To_Why.Find (Symbol_Table, Ent);
      T   : W_Expr_Id;
      Havocd : W_Expr_Id;

   begin
      --  The special cases of this function are:
      --  * parameters, whose names are stored in Params.Name_Map (these can
      --    also be refs)
      --  * enumeration literals (we have a separate function)
      --  * ids of Standard.ASCII (transform to integer)
      --  * quantified variables (use local name instead of global name)

      if Ada_Ent_To_Why.Has_Element (C) then
         T := +Ada_Ent_To_Why.Element (C).Main.B_Name;

      elsif Ekind (Ent) = E_Enumeration_Literal then
         T := Transform_Enum_Literal (Expr, Ent, Domain);

      elsif Sloc (Ent) = Standard_ASCII_Location then
         T :=
           New_Integer_Constant
             (Value => Char_Literal_Value (Constant_Value (Ent)));
      else
         Ada.Text_IO.Put_Line ("[Transform_Identifier] unregistered entity "
                               & Full_Name (Ent));
         raise Program_Error;
      end if;

      --  If we have an object with Async_Writers, we must havoc it before
      --  dereferencing it.

      if Has_Async_Writers (Direct_Mapping_Id (Ent)) then
         pragma Assert (Is_Mutable_In_Why (Ent));
         pragma Assert (Params.Ref_Allowed);
         declare
            Args : constant W_Expr_Array (1 .. 1) := W_Expr_Array'(1 => T);
         begin
            Havocd := New_Call
              (Name     => New_Identifier (Name => "__havoc"),
               Args     => Args,
               Domain   => Domain);
         end;
      end if;

      if Is_Mutable_In_Why (Ent) and then Params.Ref_Allowed then
         T := New_Deref (Ada_Node => Get_Ada_Node (+T),
                         Right    => +T,
                         Typ      => Get_Type (T));
      end if;

      if Has_Async_Writers (Direct_Mapping_Id (Ent)) then
         T := +Sequence (Left  => +Havocd,
                         Right => +T);
      end if;

      return T;
   end Transform_Identifier;

   -------------------------------------
   -- Transform_Membership_Expression --
   -------------------------------------

   function Transform_Membership_Expression
     (Params : Transformation_Params;
      Domain : EW_Domain;
      Expr   : Node_Id) return W_Expr_Id
   is

      function Transform_Alternative
        (Var       : W_Identifier_Id;
         Alt       : Node_Id;
         Base_Type : W_Type_Id)
         return W_Expr_Id;
      --  If the alternative Alt is a subtype mark, transform it as a simple
      --  membership test "Var in Alt". Otherwise transform it as an equality
      --  test "Var = Alt".

      function Transform_Simple_Membership_Expression
        (Var       : W_Identifier_Id;
         In_Expr   : Node_Id) return W_Expr_Id;

      ---------------------------
      -- Transform_Alternative --
      ---------------------------

      function Transform_Alternative
        (Var       : W_Identifier_Id;
         Alt       : Node_Id;
         Base_Type : W_Type_Id)
         return W_Expr_Id
      is
         Result : W_Expr_Id;
      begin
         if (Is_Entity_Name (Alt) and then Is_Type (Entity (Alt)))
           or else Nkind (Alt) = N_Range
         then
            Result :=
              Transform_Simple_Membership_Expression (Var, Alt);
         else
            Result := New_Comparison
              (Cmp       => EW_Eq,
               Left      => +Var,
               Right     => Transform_Expr (Expr          => Alt,
                                            Expected_Type => Base_Type,
                                            Domain        => EW_Term,
                                            Params        => Params),
               Domain    => Domain);
         end if;

         return Result;
      end Transform_Alternative;

      --------------------------------------------
      -- Transform_Simple_Membership_Expression --
      --------------------------------------------

      function Transform_Simple_Membership_Expression
        (Var       : W_Identifier_Id;
         In_Expr   : Node_Id) return W_Expr_Id
      is
         True_Expr  : constant W_Expr_Id :=
           (if Domain = EW_Pred then +True_Pred
            else
               New_Literal (Domain => EW_Term,
                            Value  => EW_True));
      begin

         --  First handle the simpler case of s subtype mark

         if Nkind (In_Expr) in N_Identifier | N_Expanded_Name
           and then Ekind (Entity (In_Expr)) in Type_Kind
         then
            declare
               Ty : constant Entity_Id := Unique_Entity (Entity (In_Expr));
            begin

               --  Record subtypes are special

               if Ekind (Ty) in Record_Kind then

                  --  eliminate trivial cases first, the membership test is
                  --  always true here.

                  if Root_Type (Ty) = Ty or else
                    not Has_Discriminants (Ty) or else
                    not Is_Constrained (Ty)
                  then
                     return True_Expr;
                  end if;

                  declare
                     Call : constant W_Expr_Id :=
                       New_Call (Domain => Domain,
                                 Name =>
                                   Prefix (M        => E_Module (Ty),
                                           W        => WNE_Range_Pred,
                                           Ada_Node => Ty),
                                 Args =>
                                   Prepare_Args_For_Subtype_Check (Ty, +Var),
                                 Typ  => EW_Bool_Type);
                  begin
                     if Domain = EW_Pred then
                        return Call;
                     else
                        return
                          New_Conditional
                            (Domain    => Domain,
                             Condition => Call,
                             Then_Part => True_Expr,
                             Else_Part =>
                               New_Literal (Domain => EW_Term,
                                            Value => EW_False),
                             Typ       => EW_Bool_Type);
                     end if;
                  end;
               else
                  pragma Assert (Is_Scalar_Type (Ty));
                  declare
                     M : constant W_Module_Id :=
                       (if Is_Standard_Boolean_Type (Ty) then Boolean_Module
                        else E_Module (Ty));
                  begin
                     return
                       New_Call (Domain => Domain,
                                 Name =>
                                   Prefix (M        => M,
                                           W        => WNE_Range_Pred,
                                           Ada_Node => Ty),
                                 Args => (1 => +Var),
                                 Typ  => EW_Bool_Type);
                  end;
               end if;
            end;
         else
            return Range_Expr (In_Expr, +Var, Domain, Params);
         end if;
      end Transform_Simple_Membership_Expression;

      Var       : constant Node_Id := Left_Opnd (Expr);
      Result    : W_Expr_Id;
      Why_Var   : W_Identifier_Id;
      Base_Type : W_Type_Id := Base_Why_Type (Var);
      Subdomain : constant EW_Domain :=
        (if Domain = EW_Pred then EW_Term else Domain);
      Var_Expr  : W_Expr_Id;

      --  Start of processing for Transform_Membership_Expression

   begin

      --  For ranges and membership, "bool" should be mapped to "int".

      if Base_Type = EW_Bool_Type then
         Base_Type := EW_Int_Type;
      end if;
      Why_Var := New_Temp_Identifier (Typ => Base_Type);
      Var_Expr := Transform_Expr (Var, Base_Type, Subdomain, Params);

      if Present (Alternatives (Expr)) then
         declare
            Alt : Node_Id;
         begin
            Alt := Last (Alternatives (Expr));
            Result := Transform_Alternative (Why_Var, Alt, Base_Type);

            Prev (Alt);
            while Present (Alt) loop
               Result := New_Or_Else_Expr
                 (Left   => Transform_Alternative (Why_Var, Alt, Base_Type),
                  Right  => Result,
                  Domain => Domain);
               Prev (Alt);
            end loop;
         end;

      else
         Result :=
           Transform_Simple_Membership_Expression (Why_Var, Right_Opnd (Expr));
      end if;

      --  Inverse the result if the operator is NOT IN

      if Nkind (Expr) = N_Not_In then
         if Domain = EW_Term then
            Result := New_Call
              (Ada_Node => Expr,
               Domain   => Domain,
               Name     => New_Identifier (Name => "notb"),
               Args     => (1 => Result),
               Typ      => EW_Bool_Type);

         else
            Result := New_Not (Right  => Result, Domain => Domain);
         end if;
      end if;

      Result :=
        New_Typed_Binding
          (Domain => Domain,
           Name   => Why_Var,
           Def    => +Var_Expr,
           Context => Result);

      return Result;
   end Transform_Membership_Expression;

   ----------------------
   -- Transform_Pragma --
   ----------------------

   function Transform_Pragma (Prag : Node_Id) return W_Prog_Id is
      Pname   : constant Name_Id   := Pragma_Name (Prag);
      Prag_Id : constant Pragma_Id := Get_Pragma_Id (Pname);

   begin
      case Prag_Id is

         --  Ignore pragma Check for preconditions and postconditions

         when Pragma_Check =>
            return Transform_Pragma_Check (Prag);

         --  Pragma Overflow_Mode should have an effect on proof, but is
         --  currently ignored (and a corresponding warning is issued
         --  during marking).

         when Pragma_Overflow_Mode =>
            return New_Void (Prag);

         --  Ignore pragmas which have no effect on proof, or whose effect
         --  is taken into account elsewhere (e.g. contract, loop variant).

         when Pragma_Abstract_State               |
              Pragma_Ada_83                       |
              Pragma_Ada_95                       |
              Pragma_Ada_05                       |
              Pragma_Ada_2005                     |
              Pragma_Ada_12                       |
              Pragma_Ada_2012                     |
              Pragma_Annotate                     |
              Pragma_Assertion_Policy             |
              Pragma_Async_Readers                |
              Pragma_Async_Writers                |
              Pragma_Check_Policy                 |
              Pragma_Contract_Cases               |
              Pragma_Convention                   |
              Pragma_Depends                      |
              Pragma_Effective_Reads              |
              Pragma_Effective_Writes             |
              Pragma_Elaborate                    |
              Pragma_Elaborate_All                |
              Pragma_Elaborate_Body               |
              Pragma_Export                       |
              Pragma_External                     |
              Pragma_Global                       |
              Pragma_Import                       |
              Pragma_Initial_Condition            |
              Pragma_Initializes                  |
              Pragma_Inline                       |
              Pragma_Inline_Always                |
              Pragma_Inspection_Point             |
              Pragma_Linker_Options               |
              Pragma_List                         |
              Pragma_Loop_Variant                 |
              Pragma_No_Return                    |
              Pragma_Optimize                     |
              Pragma_Pack                         |
              Pragma_Page                         |
              Pragma_Part_Of                      |
              Pragma_Postcondition                |
              Pragma_Precondition                 |
              Pragma_Preelaborable_Initialization |
              Pragma_Preelaborate                 |
              Pragma_Pure                         |
              Pragma_Pure_Function                |
              Pragma_Refined_Depends              |
              Pragma_Refined_Global               |
              Pragma_Refined_Post                 |
              Pragma_Refined_State                |
              Pragma_Reviewable                   |
              Pragma_SPARK_Mode                   |
              Pragma_Style_Checks                 |
              Pragma_Test_Case                    |
              Pragma_Unmodified                   |
              Pragma_Unreferenced                 |
              Pragma_Validity_Checks              |
              Pragma_Volatile                     |
              Pragma_Warnings                     =>
            return New_Void (Prag);

         --  Pragmas which should not reach here

         when Pragma_Loop_Invariant =>
            raise Program_Error;

         --  Ignore other pragmas with a warning

         when others =>
            Error_Msg_Name_1 := Pragma_Name (Prag);
            Error_Msg_N ("?pragma % is not yet supported in proof", Prag);
            Error_Msg_N ("\\it is currently ignored", Prag);
            return New_Void (Prag);
      end case;
   end Transform_Pragma;

   ----------------------------
   -- Transform_Pragma_Check --
   ----------------------------

   procedure Transform_Pragma_Check
     (Stmt    : Node_Id;
      Runtime : out W_Prog_Id;
      Pred    : out W_Pred_Id)
   is
      Arg1 : constant Node_Id := First (Pragma_Argument_Associations (Stmt));
      Arg2 : constant Node_Id := Next (Arg1);
      Expr : constant Node_Id := Expression (Arg2);
      Params : Transformation_Params := Assert_Params;
   begin

      --  Pragma Check generated for Pre/Postconditions are
      --  ignored.

      if Chars (Get_Pragma_Arg (Arg1)) = Name_Precondition
           or else
         Chars (Get_Pragma_Arg (Arg1)) = Name_Postcondition
      then
         Runtime := New_Void (Stmt);
         Pred := True_Pred;
         return;
      end if;

      if Present (Expr) then
         Runtime := New_Ignore
           (Prog => +Transform_Expr (Expr, EW_Prog, Params => Params));
         Params.Gen_Image := True;
         Pred := +Transform_Expr (Expr, EW_Pred, Params => Params);
         return;
      else
         raise Program_Error;
      end if;
   end Transform_Pragma_Check;

   function Transform_Pragma_Check (Prag : Node_Id) return W_Prog_Id is
      Check_Expr : W_Prog_Id;
      Pred       : W_Pred_Id;

      --  Mark non-selected loop invariants (those not occurring
      --  next to the first batch of selected variants and
      --  invariants) as loop invariant VCs.

      Reason : constant VC_Kind :=
        (if Is_Pragma_Check (Prag, Name_Loop_Invariant)
         then VC_Loop_Invariant
         else VC_Assert);

      T : W_Prog_Id;
   begin

      --  pre and post are not handled here

      if Is_Pragma_Check (Prag, Name_Precondition)
        or else
          Is_Pragma_Check (Prag, Name_Pre)
        or else
          Is_Pragma_Check (Prag, Name_Postcondition)
        or else
          Is_Pragma_Check (Prag, Name_Post)
      then
         return New_Void (Prag);
      end if;

      Transform_Pragma_Check (Prag, Check_Expr, Pred);

      --  assert and cut is not handled here, except for runtime errors.

      if Is_Pragma_Assert_And_Cut (Prag) then
         if Check_Expr /= Why_Empty then
            return Check_Expr;
         else
            return New_Void (Prag);
         end if;
      end if;

      --  get rid of simple cases true and false

      if Is_False_Boolean (+Pred) then
         return
           +New_VC_Expr
           (Ada_Node => Prag,
            Expr     => +New_Identifier (Name => "absurd"),
            Reason   => Reason,
            Domain   => EW_Prog);
      elsif Is_True_Boolean (+Pred) then
         return New_Void (Prag);
      end if;

      --  now handle remaining cases of "regular" pragma Check/Assert and
      --  pragma Assume

      if Is_Pragma_Check (Prag, Name_Assume) then
         T := New_Assume_Statement (Post => Pred);
      else
         T := New_Located_Assert (Prag, Pred, Reason);
      end if;

      if Check_Expr /= Why_Empty then
         T := Sequence (Check_Expr, T);
      end if;

      return T;
   end Transform_Pragma_Check;

   -------------------------------------
   -- Transform_Quantified_Expression --
   -------------------------------------

   function Transform_Quantified_Expression
     (Expr   : Node_Id;
      Domain : EW_Domain;
      Params : Transformation_Params) return W_Expr_Id
   is
      -----------------------
      -- Local Subprograms --
      -----------------------

      function Extract_Index_Entity
        (N          : Node_Id;
         Over_Range : Boolean) return Entity_Id;
      --  Return the entity used for indexing in the quantification

      function Extract_Set_Node
        (N          : Node_Id;
         Over_Range : Boolean) return Node_Id;
      --  Return the set over which the quantification is performed

      --------------------------
      -- Extract_Index_Entity --
      --------------------------

      function Extract_Index_Entity
        (N          : Node_Id;
         Over_Range : Boolean) return Entity_Id
      is
      begin
         if Over_Range then
            return Defining_Identifier (Loop_Parameter_Specification (N));
         else
            return Defining_Identifier (Iterator_Specification (N));
         end if;
      end Extract_Index_Entity;

      ----------------------
      -- Extract_Set_Node --
      ----------------------

      function Extract_Set_Node
        (N          : Node_Id;
         Over_Range : Boolean) return Node_Id
      is
      begin
         if Over_Range then
            return
              Discrete_Subtype_Definition (Loop_Parameter_Specification (N));
         else
            return Get_Container_In_Iterator_Specification
              (Iterator_Specification (N));
         end if;
      end Extract_Set_Node;

      Over_Range : constant Boolean :=
                     Present (Loop_Parameter_Specification (Expr));
      --  The quantification is either over a scalar range, in which case
      --  there is a loop-parameter-specification component, otherwise
      --  the quantification is over a container and there is an
      --  iterator-specification component.

      Index_Ent  : constant Entity_Id :=
        Extract_Index_Entity (Expr, Over_Range);
      Range_E    : constant Node_Id   := Extract_Set_Node (Expr, Over_Range);
      Index_Type : constant Entity_Id := Etype (Index_Ent);
      Index_Base : constant W_Type_Id :=
        (if Over_Range then EW_Int_Type
         else EW_Abstract (Index_Type));
      Cond_Expr  : W_Expr_Id;
      Why_Id     : constant W_Identifier_Id :=
        New_Identifier (Name => Full_Name (Index_Ent),
                        Typ  => Index_Base);
      Index_Id   : constant W_Expr_Id :=
        (if Over_Range then +Why_Id
         else Insert_Checked_Conversion
           (Ada_Node => Index_Ent,
            Ada_Type => Index_Type,
            Domain   => EW_Term,
            Expr     => +Why_Id,
            To       => (if Use_Why_Base_Type (Index_Ent) then
                            Base_Why_Type (Unique_Entity (Index_Type))
                         else Type_Of_Node (Index_Ent))));
      --  Start of Transform_Quantified_Expression

   begin

      if Domain = EW_Term then

         --  It is trivial to promote a predicate to a term, by doing
         --    if pred then True else False

         declare
            Pred : constant W_Expr_Id :=
                     Transform_Quantified_Expression
                       (Expr, EW_Pred, Params);
         begin
            return
              New_Conditional (Domain    => EW_Term,
                               Condition => Pred,
                               Then_Part =>
                                 New_Literal (Value => EW_True,
                                              Domain => Domain,
                                              Ada_Node => Standard_Boolean),
                               Else_Part =>
                                 New_Literal (Value => EW_False,
                                              Domain => Domain,
                                              Ada_Node => Standard_Boolean),
                               Typ       => EW_Bool_Type);
         end;
      end if;

      --  We are now in domain Prog or Pred, and have to translate the
      --  condition of the quantified expression, where the context is
      --  enriched by the loop parameter

      Ada_Ent_To_Why.Push_Scope (Symbol_Table);
      Insert_Entity (Index_Ent, Why_Id);
      Cond_Expr := Transform_Expr (Condition (Expr), Domain, Params);
      Ada_Ent_To_Why.Pop_Scope (Symbol_Table);

      --  In the predicate case the quantification in Ada is translated as a
      --  quantification in Why3.

      if Domain = EW_Pred then
         declare
            Constraint : constant W_Pred_Id :=
              (if Over_Range then
                 +Range_Expr (Range_E, +Why_Id, EW_Pred, Params)
               else
               +Has_Element_Expr (Range_E, +Index_Id, EW_Pred, Params));
            Connector  : constant EW_Connector :=
              (if All_Present (Expr) then EW_Imply else EW_And);
            Quant_Body : constant W_Pred_Id :=
              New_Connection
                (Op     => Connector,
                 Left   => +Constraint,
                 Right  => Cond_Expr);
         begin
            if All_Present (Expr) then
               return
                  New_Universal_Quantif
                     (Ada_Node  => Expr,
                      Variables => (1 => Why_Id),
                      Labels    => Name_Id_Sets.Empty_Set,
                      Var_Type  => Index_Base,
                      Pred      => Quant_Body);
            else
               return
                  New_Existential_Quantif
                     (Ada_Node  => Expr,
                      Variables => (1 => Why_Id),
                      Labels    => Name_Id_Sets.Empty_Set,
                      Var_Type  => Index_Base,
                      Pred      => Quant_Body);
            end if;
         end;

      --  We are interested in the checks for the entire range, and
      --  in the return value of the entire expression, but we are
      --  not interested in the exact order in which things are
      --  evaluated. We also do not want to translate the expression
      --  function by a loop. So our scheme is the following:
      --    for all I in Cond => Expr
      --
      --  becomes:
      --    (let i = ref [ int ] in
      --       if cond then ignore (expr));
      --    [ { } bool { result = true <-> expr } ]
      --  The condition is a formula that expresses that i is in the
      --  range given by the quantification.

      elsif Domain = EW_Prog then
         declare
            Range_Cond : W_Prog_Id;
         begin
            Range_Cond :=
              (if Over_Range then
                 +Range_Expr (Range_E, +Why_Id, EW_Prog, Params)
               else
                 +Has_Element_Expr (Range_E, +Index_Id, EW_Prog, Params));
            return
              +Sequence
                (+New_Typed_Binding
                   (Name    => Why_Id,
                    Domain  => EW_Prog,
                    Def     =>
                      +New_Simpl_Any_Prog (Index_Base),
                    Context =>
                      New_Conditional
                        (Domain    => EW_Prog,
                         Condition => +Range_Cond,
                         Then_Part => +New_Ignore (Prog => +Cond_Expr))),
                 New_Assume_Statement
                   (Ada_Node    => Expr,
                    Return_Type => EW_Bool_Type,
                    Post        =>
                      +W_Expr_Id'(New_Connection
                        (Domain   => EW_Pred,
                         Left     =>
                           New_Relation
                             (Domain   => EW_Pred,
                              Op_Type  => EW_Bool,
                              Left     => +New_Result_Ident (EW_Bool_Type),
                              Op       => EW_Eq,
                              Right    => +True_Term),
                         Op       => EW_Equivalent,
                         Right    =>
                           +Transform_Expr (Expr, EW_Pred, Params)))));
         end;
      else

         --  case Domain = EW_Term already handled

         raise Program_Error;
      end if;
   end Transform_Quantified_Expression;

   ---------------------
   -- Transform_Raise --
   ---------------------

   function Transform_Raise (Stat : Node_Id) return W_Prog_Id is
   begin
      case Nkind (Stat) is
         when N_Raise_xxx_Error =>
            case RT_Exception_Code'Val
              (Uintp.UI_To_Int (Reason (Stat)))
            is
               when CE_Discriminant_Check_Failed =>
                  return +New_VC_Expr (Domain   => EW_Prog,
                                       Ada_Node => Stat,
                                       Expr     =>
                                          +New_Identifier (Name => "absurd"),
                                       Reason   => VC_Discriminant_Check);
               when others =>
                  raise Program_Error;
            end case;

         when N_Raise_Statement =>
            return
              New_Assert
                (Pred =>
                    New_Label
                   (Labels => New_VC_Labels (Stat, VC_Raise),
                    Def    => +False_Pred));

         when others =>
            raise Program_Error;
      end case;
   end Transform_Raise;

   ---------------------------------------------
   -- Transform_Record_Component_Associations --
   ---------------------------------------------

   function Transform_Record_Component_Associations
     (Domain              : EW_Domain;
      Typ                 : Entity_Id;
      Assocs              : List_Id;
      Params              : Transformation_Params;
      In_Attribute_Update : Boolean := False) return W_Field_Association_Array
   is
      function Components_Count (Assocs : List_Id) return Natural;
      --  Returns the number of component selectors in Assocs

      ----------------------
      -- Components_Count --
      ----------------------

      function Components_Count (Assocs : List_Id) return Natural is
         CL          : List_Id;
         Association : Node_Id := Nlists.First (Assocs);
         Associated_Components : Natural := 0;
      begin
         while Present (Association) loop
            CL := Choices (Association);
            Associated_Components := Associated_Components +
              Integer (List_Length (CL));
            Next (Association);
         end loop;
         return Associated_Components;
      end Components_Count;

      Component   : Entity_Id;
      Association : Node_Id;
      Result      :
        W_Field_Association_Array (1 .. Integer (Components_Count (Assocs)));
      J           : Positive := Result'First;
      CL          : List_Id;
      Choice      : Node_Id;

   --  Start of Transform_Record_Component_Associations

   begin
      --  Normal record aggregates are required to be fully initialized, but
      --  'Update aggregates are allowed to be partial. The implementation here
      --  is general enough for both kinds of aggregates so the association
      --  list does not necessarily cover all the components.

      pragma Assert
        (In_Attribute_Update
          or else Number_Components (Typ) = Integer (List_Length (Assocs)));

      Association := Nlists.First (Assocs);
      pragma Assert (Present (Association));

      --  Start with the first component
      CL := Choices (Association);
      --  normal, fully defined aggregate, has singleton choice lists
      pragma Assert (In_Attribute_Update or else List_Length (CL) = 1);
      Choice := First (CL);

      --  Loop over the associations and component choice lists
      while Present (Choice) loop
         declare
            Expr : W_Expr_Id;
         begin
            --  We don't expect "others" for 'Update aggregates (illegal). For
            --  normal aggregates occurances of "others" have been removed from
            --  the AST wich will have an association list is as long as the
            --  number of components, and with only singleton choice lists.

            pragma Assert (Nkind (Choice) /= N_Others_Choice);

            Component := Search_Component_By_Name (Typ, Choice);

            if not Box_Present (Association) then
               Expr := Transform_Expr
                         (Expr          => Expression (Association),
                          Expected_Type => EW_Abstract (Etype (Component)),
                          Domain        => Domain,
                          Params        => Params);
            else
               pragma Assert (Domain = EW_Prog);
               Expr := +New_Simpl_Any_Prog
                         (T => EW_Abstract (Etype (Component)));
            end if;

            Result (J) := New_Field_Association
                            (Domain => Domain,
                             Field  => To_Why_Id (Component),
                             Value  => Expr);
            J := J + 1;

            --  Getting the next component from the associations' component
            --  lists, which may require selecting the next choice (for
            --  attribute Update), or selecting the next component association.

            Next (Choice);
            if No (Choice) then
               Next (Association);
               if Present (Association) then
                  CL := Choices (Association);
                  pragma Assert (In_Attribute_Update
                                  or else List_Length (CL) = 1);
                  Choice := First (CL);
               end if;
            end if;
         end;
      end loop;

      pragma Assert (No (Association));
      return Result;
   end Transform_Record_Component_Associations;

   ----------------------------------------
   -- Transform_Statement_Or_Declaration --
   ----------------------------------------

   function Transform_Statement_Or_Declaration
     (Stmt_Or_Decl   : Node_Id;
      Assert_And_Cut : out W_Pred_Id) return W_Prog_Id is
   begin
      --  Make sure that Assert_And_Cut is initialized

      Assert_And_Cut := Why_Empty;

      case Nkind (Stmt_Or_Decl) is
         when N_Label | N_Null_Statement =>
            return New_Void (Stmt_Or_Decl);

         when N_Assignment_Statement =>

            return Transform_Assignment_Statement (Stmt_Or_Decl);

         --  Translate a return statement by raising the predefined exception
         --  for returns, which is caught at the end of the subprogram. For
         --  functions, store the value returned in the local special variable
         --  for returned values, prior to raising the exception.

         when N_Simple_Return_Statement =>
            declare
               Raise_Stmt  : constant W_Prog_Id :=
                 New_Raise
                   (Ada_Node => Stmt_Or_Decl,
                    Name     => To_Ident (WNE_Result_Exc),
                    Typ      => EW_Unit_Type);
               Result_Stmt : W_Prog_Id;
            begin
               if Expression (Stmt_Or_Decl) /= Empty then
                  declare
                     Return_Type : constant W_Type_Id :=
                       Type_Of_Node (Etype (Return_Applies_To
                         (Return_Statement_Entity (Stmt_Or_Decl))));
                  begin
                     Result_Stmt :=
                       New_Assignment
                         (Ada_Node => Stmt_Or_Decl,
                          Name     => Name_For_Result,
                          Value    =>
                            +Transform_Expr (Expression (Stmt_Or_Decl),
                                             Return_Type,
                                             EW_Prog,
                                             Params => Body_Params));
                     return Sequence (Result_Stmt, Raise_Stmt);
                  end;
               else
                  return Raise_Stmt;
               end if;
            end;

         when N_Extended_Return_Statement =>
            declare
               Raise_Stmt  : constant W_Prog_Id :=
                 New_Raise
                   (Ada_Node => Stmt_Or_Decl,
                    Name     => To_Ident (WNE_Result_Exc));
               Expr        : W_Prog_Id :=
                 Transform_Statements_And_Declarations
                   (Return_Object_Declarations (Stmt_Or_Decl));
               Ret_Obj     : constant Entity_Id :=
                 Get_Return_Object_Entity (Stmt_Or_Decl);
               Obj_Deref   : constant W_Prog_Id :=
                 +Insert_Simple_Conversion
                   (Domain => EW_Prog,
                    Expr   =>
                      New_Deref
                      (Right => To_Why_Id (E => Ret_Obj),
                       Typ   => Why_Type_Of_Entity (Ret_Obj)),
                    To     => EW_Abstract (Etype (Current_Subp)));
            begin
               Expr :=
                 Sequence
                   (Expr,
                    Transform_Statements_And_Declarations
                      (Statements
                         (Handled_Statement_Sequence (Stmt_Or_Decl))));
               Expr :=
                 Sequence
                   (Expr,
                    New_Assignment
                      (Name  => Name_For_Result,
                       Value => Obj_Deref));
               return Sequence (Expr, Raise_Stmt);
            end;

         when N_Procedure_Call_Statement =>
            declare
               Nb_Of_Refs : Natural;
               Args       : constant W_Expr_Array :=
                 Compute_Call_Args
                   (Stmt_Or_Decl, EW_Prog, Nb_Of_Refs, Params => Body_Params);
               Subp       : constant Entity_Id := Entity (Name (Stmt_Or_Decl));
               Why_Name   : constant W_Identifier_Id :=
                 To_Why_Id (Subp, EW_Prog);
               Call       : W_Expr_Id;
            begin
               if Why_Subp_Has_Precondition (Subp) then
                  Call :=
                    +New_VC_Call
                      (Stmt_Or_Decl,
                       Why_Name,
                       Args,
                       VC_Precondition,
                       EW_Prog,
                       EW_Unit_Type);
               else
                  Call :=
                    New_Call
                      (Stmt_Or_Decl,
                       EW_Prog,
                       Why_Name,
                       Args,
                       EW_Unit_Type);
               end if;

               if Nb_Of_Refs = 0 then
                  return +Call;
               else
                  return Insert_Ref_Context
                           (Body_Params, Stmt_Or_Decl, +Call, Nb_Of_Refs);
               end if;
            end;

         when N_If_Statement =>
            declare
               Tail : W_Prog_Id := Transform_Statements_And_Declarations
                                     (Else_Statements (Stmt_Or_Decl));
            begin
               if Present (Elsif_Parts (Stmt_Or_Decl)) then
                  declare
                     Cur : Node_Id := Last (Elsif_Parts (Stmt_Or_Decl));
                  begin

                     --  Beginning from the tail that consists of the
                     --  translation of the Else part, possibly a no-op,
                     --  translate the list of elsif parts into a chain of
                     --  if-then-else Why expressions.

                     while Present (Cur) loop
                        Tail :=
                          New_Label
                            (Labels =>
                               Name_Id_Sets.To_Set
                                 (New_Located_Label
                                    (Cur, Is_VC => False)),
                             Def    =>
                             +New_Simpl_Conditional
                               (Condition =>
                                  Transform_Expr_With_Actions
                                    (Condition (Cur),
                                     Condition_Actions (Cur),
                                     EW_Bool_Type,
                                     EW_Prog,
                                     Params => Body_Params),
                                Then_Part =>
                                  +Transform_Statements_And_Declarations
                                    (Then_Statements (Cur)),
                                Else_Part => +Tail,
                                Domain    => EW_Prog),
                                Typ       => EW_Unit_Type);
                        Prev (Cur);
                     end loop;
                  end;
               end if;

               --  Finish by putting the main if-then-else on top.

               return
                 +New_Simpl_Conditional
                 (Condition => Transform_Expr (Condition (Stmt_Or_Decl),
                                               EW_Bool_Type,
                                               EW_Prog,
                                               Params => Body_Params),
                    Then_Part =>
                      +Transform_Statements_And_Declarations
                        (Then_Statements (Stmt_Or_Decl)),
                    Else_Part => +Tail,
                    Domain    => EW_Prog);
            end;

         when N_Object_Declaration    |
              N_Subtype_Declaration   |
              N_Full_Type_Declaration =>
            return Transform_Declaration (Stmt_Or_Decl);

         when N_Loop_Statement =>
            return Transform_Loop_Statement (Stmt_Or_Decl);

         when N_Exit_Statement =>
            return Transform_Exit_Statement (Stmt_Or_Decl);

         when N_Case_Statement =>
            return
              +Case_Expr_Of_Ada_Node
                 (N           => Stmt_Or_Decl,
                  Domain      => EW_Prog,
                  Params      => Body_Params);

         when N_Block_Statement =>
            return Transform_Block_Statement (Stmt_Or_Decl);

         when N_Pragma =>
            if Is_Pragma_Assert_And_Cut (Stmt_Or_Decl) then
               declare
                  Check_Expr : W_Prog_Id;
                  Pred       : W_Pred_Id;
               begin
                  Transform_Pragma_Check (Stmt_Or_Decl, Check_Expr, Pred);
                  Assert_And_Cut := Pred;
               end;
            end if;

            return Transform_Pragma (Stmt_Or_Decl);

         when N_Raise_xxx_Error | N_Raise_Statement =>
            return Transform_Raise (Stmt_Or_Decl);

         --  Freeze nodes do not have any impact on proof

         when N_Freeze_Entity =>
            return New_Void;

         --  Renamings are replaced by the renamed object in the frontend, but
         --  the renaming objects are not removed from the tree. We can safely
         --  ignore them.

         when N_Object_Renaming_Declaration =>
            return New_Void;

         --  Nothing to do for an implicit label declaration

         when N_Implicit_Label_Declaration =>
            return New_Void;

         --  Subprogram declarations are already taken care of explicitly.
         --  They should not be treated as part of a list of declarations.

         when N_Subprogram_Body        |
              N_Subprogram_Declaration =>
            return New_Void;

         when others =>
            Ada.Text_IO.Put_Line ("[Transform_Statement] kind ="
                                  & Node_Kind'Image (Nkind (Stmt_Or_Decl)));
            raise Not_Implemented;
      end case;
   end Transform_Statement_Or_Declaration;

   ------------------------------------------------
   -- Transform_Statement_Or_Declaration_In_List --
   ------------------------------------------------

   function Transform_Statement_Or_Declaration_In_List
     (Stmt_Or_Decl : Node_Id;
      Prev_Prog    : W_Prog_Id) return W_Prog_Id
   is
      Result        : W_Prog_Id := Prev_Prog;
      Cut_Assertion : W_Pred_Id;
      Prog          : constant W_Prog_Id :=
        Transform_Statement_Or_Declaration (Stmt_Or_Decl, Cut_Assertion);
   begin
      Result :=
        Sequence
          (Result,
           New_Label (Labels =>
                            Name_Id_Sets.To_Set
                        (New_Located_Label
                           (Stmt_Or_Decl,
                            Is_VC => False)),
                      Def    => +Prog));
      if Cut_Assertion /= Why_Empty then
         Result :=
           New_Located_Abstract
             (Ada_Node => Stmt_Or_Decl,
              Expr     => +Result,
              Post     => Cut_Assertion,
              Reason   => VC_Assert);
      end if;

      return Result;
   end Transform_Statement_Or_Declaration_In_List;

   -------------------------------------------
   -- Transform_Statements_And_Declarations --
   -------------------------------------------

   function Transform_Statements_And_Declarations
     (Stmts_And_Decls : List_Of_Nodes.List) return W_Prog_Id
   is
      Result : W_Prog_Id := New_Void;
   begin
      for Cur_Stmt_Or_Decl of Stmts_And_Decls loop
         Result :=
           Transform_Statement_Or_Declaration_In_List
             (Stmt_Or_Decl => Cur_Stmt_Or_Decl,
              Prev_Prog    => Result);
      end loop;
      return Result;
   end Transform_Statements_And_Declarations;

   function Transform_Statements_And_Declarations
     (Stmts_And_Decls : List_Id) return W_Prog_Id
   is
     (Transform_Statements_And_Declarations
        (Get_Statement_And_Declaration_List (Stmts_And_Decls)));

   ------------------------------
   -- Transform_String_Literal --
   ------------------------------

   procedure Transform_String_Literal
     (Params : Transformation_Params;
      N      : Node_Id)
   is
      Name      : constant String := New_Temp_Identifier;
      Ty        : constant Entity_Id := Type_Of_Node (N);
      Why_Type  : constant W_Type_Id := New_Abstract_Base_Type (Ty);
      Id        : constant W_Identifier_Id :=
        New_Identifier (Ada_Node => N,
                        Name     => Name,
                        Typ      => Why_Type);
      Decl_File : Why_Section := Why_Sections (Dispatch_Entity (N));
   begin
      if Params.File = Decl_File.File then
         Decl_File.Cur_Theory := Why_Empty;
      end if;

      Open_Theory (Decl_File, Name,
                   Comment =>
                     "Module for defining a value for string literal "
                       & (if Sloc (N) > 0 then
                            " defined at " & Build_Location_String (Sloc (N))
                          else "")
                       & ", created in " & GNAT.Source_Info.Enclosing_Entity);
      Emit
        (Decl_File.Cur_Theory,
         Why.Atree.Builders.New_Function_Decl
           (Domain      => EW_Term,
            Name        => Id,
            Labels      => Name_Id_Sets.Empty_Set,
            Binders     => (1 .. 0 => <>),
            Return_Type => Why_Type));
      Close_Theory (Decl_File,
                    Kind => Definition_Theory,
                    Defined_Entity => N);

      if Params.File = Decl_File.File then
         Decl_File.Cur_Theory := Params.Theory;
      end if;

      Insert_Extra_Module (N,
                           New_Module (File => No_Name, Name => NID (Name)));
   end Transform_String_Literal;

   -------------------------------
   -- Why_Subp_Has_Precondition --
   -------------------------------

   function Why_Subp_Has_Precondition (E : Entity_Id) return Boolean is
   begin
      return Has_Contracts (E, Name_Precondition) or else
        Entity_In_External_Axioms (E) or else
        No_Return (E);
   end Why_Subp_Has_Precondition;

end Gnat2Why.Expr;
