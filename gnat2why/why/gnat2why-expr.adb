------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                        G N A T 2 W H Y - E X P R                         --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                       Copyright (C) 2010-2015, AdaCore                   --
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

with Ada.Containers;         use Ada.Containers;
with Ada.Strings.Equal_Case_Insensitive;
with Ada.Text_IO;  --  For debugging, to print info before raising an exception
with Checks;                 use Checks;
with Einfo;                  use Einfo;
with Elists;                 use Elists;
with Errout;                 use Errout;
with Flow_Dependency_Maps;   use Flow_Dependency_Maps;
with Flow_Generated_Globals; use Flow_Generated_Globals;
with Flow_Refinement;        use Flow_Refinement;
with Flow_Utility;           use Flow_Utility;
with GNAT.Source_Info;
with Gnat2Why.Expr.Loops;    use Gnat2Why.Expr.Loops;
with Gnat2Why.Subprograms;   use Gnat2Why.Subprograms;
with Namet;                  use Namet;
with Nlists;                 use Nlists;
with Opt;
with Rtsfind;                use Rtsfind;
with Sem_Aux;                use Sem_Aux;
with Sem_Disp;               use Sem_Disp;
with Sem_Util;               use Sem_Util;
with Sem_Type;               use Sem_Type;
with Sinput;                 use Sinput;
with Snames;                 use Snames;
with SPARK_Definition;       use SPARK_Definition;
with SPARK_Frame_Conditions; use SPARK_Frame_Conditions;
with Stand;                  use Stand;
with System;                 use System;
with Uintp;                  use Uintp;
with Urealp;                 use Urealp;
with VC_Kinds;               use VC_Kinds;
with Why;                    use Why;
with Why.Atree.Builders;     use Why.Atree.Builders;
with Why.Atree.Accessors;    use Why.Atree.Accessors;
with Why.Atree.Mutators;     use Why.Atree.Mutators;
with Why.Atree.Modules;      use Why.Atree.Modules;
with Why.Conversions;        use Why.Conversions;
with Why.Gen.Arrays;         use Why.Gen.Arrays;
with Why.Gen.Binders;        use Why.Gen.Binders;
with Why.Gen.Consts;         use Why.Gen.Consts;
with Why.Gen.Decl;           use Why.Gen.Decl;
with Why.Gen.Expr;           use Why.Gen.Expr;
with Why.Gen.Names;          use Why.Gen.Names;
with Why.Gen.Preds;          use Why.Gen.Preds;
with Why.Gen.Progs;          use Why.Gen.Progs;
with Why.Gen.Records;        use Why.Gen.Records;
with Why.Unchecked_Ids;      use Why.Unchecked_Ids;

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
     (Op     : N_Op;
      E      : Entity_Id;
      T      : W_Expr_Id;
      Domain : EW_Domain) return W_Expr_Id;
   --  If E is a modular type, apply a modulus on T. If E is a floating-point
   --  type, apply the corresponding rounding operation. If E is neither,
   --  return T unchanged.
   --  Beware that for additions, substractions and multiplications on a
   --  modular type with a modulus that is not a power of two, it is not
   --  correct to use this function. Instead, one should directly use
   --  "Transform_Non_Binary_Modular_Operation" to deal with the whole
   --  transformation.
   --  Optimization: if E is a modular type, and Op is division, do not add the
   --  modulus operation.

   function Boolean_Prog_Of_Pred (W : W_Pred_Id) return W_Prog_Id is
     (New_Any_Expr (Post        =>
                      New_Connection
                        (Left     =>
                            New_Call (Domain => EW_Pred,
                                      Name   => Why_Eq,
                                      Typ    => EW_Bool_Type,
                                      Args   =>
                                        (+New_Result_Ident (EW_Bool_Type),
                                         +True_Term)),
                         Op       => EW_Equivalent,
                         Right    => +W),
                    Return_Type => EW_Bool_Type));

   --  @param W a Why3 pred expression
   --  @return the equivalent Why3 prog expression

   function Boolean_Term_Of_Pred (W : W_Pred_Id) return W_Term_Id is
     (New_Conditional (Condition => +W,
                       Then_Part => +True_Term,
                       Else_Part => +False_Term,
                       Typ       => EW_Bool_Type));
   --  @param W a Why3 pred expression
   --  @return the equivalent Why3 term expression

   function Boolean_Expr_Of_Pred
     (W      : W_Pred_Id;
      Domain : EW_Domain) return W_Expr_Id
   is
     (case Domain is
        when EW_Prog | EW_Pterm => +Boolean_Prog_Of_Pred (W),
        when EW_Term => +Boolean_Term_Of_Pred (W),
        when EW_Pred => +W);
   --  @param W a Why3 pred expression
   --  @param Domain translation domain
   --  @return the equivalent Why3 expression, depending on the [Domain]

   function Pred_Of_Boolean_Term (W : W_Term_Id) return W_Pred_Id is
     (New_Call (Name => Why_Eq,
                Args => (1 => +W, 2 => +True_Term),
                Typ  => EW_Bool_Type));
   --  @param W a Why3 term expression
   --  @return the equivalent Why3 pred expression

   function Case_Expr_Of_Ada_Node
     (N             : Node_Id;
      Expected_Type : W_Type_OId := Why_Empty;
      Domain        : EW_Domain;
      Params        : Transformation_Params) return W_Expr_Id;
   --  Build Case expression of Ada Node.

   function Compute_Call_Args
     (Call        :     Node_Id;
      Domain      :     EW_Domain;
      Nb_Of_Refs  : out Natural;
      Nb_Of_Lets  : out Natural;
      Params      :     Transformation_Params) return W_Expr_Array;
   --  Compute arguments for a function call or procedure call. The node in
   --  argument must have a "Name" field and a "Parameter_Associations" field.
   --  Nb_Of_Refs is the number of ref arguments that could not be
   --  translated "as is" (because of a type mismatch) and for which
   --  Insert_Ref_Context must be called.

   function Compute_Default_Check
     (Ty     : Entity_Id;
      Params : Transformation_Params) return W_Prog_Id;
   --  Compute Why3 code to check for absence of runtime errors in default
   --  initialization of Expr of type Ty.

   function Compute_Tag_Check
     (Call   : Node_Id;
      Params : Transformation_Params) return W_Prog_Id;

   function Compute_Attach_Handler_Check
     (Ty     : Entity_Id;
      Params : Transformation_Params) return W_Prog_Id
     with Pre => Is_Protected_Type (Ty);
   --  @param Ty a protected type
   --  @return an assertion (if necessary) that checks if any of the
   --    Attach_Handler pragmas of the procedures of the type is reserved
   --    see also Ada RM C.3.1(10/3)

   function Declaration_Is_Associated_To_Parameter
     (N : Node_Id) return Boolean
     with Pre => Present (N);
   --  Returns True if N has a Related_Expression attribute associated to
   --  a parameter entity.

   function Discrete_Choice_Is_Range (Choice : Node_Id) return Boolean;
   --  Return whether Choice is a range ("others" counts as a range)

   function Expected_Type_Of_Prefix (N : Node_Id) return W_Type_Id;
   --  The node in argument is the target of an assignment. This function
   --  computes the type of the entity that corresponds to the access.
   --  This may be different from the Etype of the node in case of
   --  unconstrained array types, or discriminant records.

   function Insert_Overflow_Check
     (Ada_Node : Node_Id;
      T        : W_Expr_Id;
      In_Type  : Entity_Id) return W_Expr_Id
     with Pre => Is_Scalar_Type (In_Type);
   --  Inserts an overflow check on top of the Why expression T, using the
   --  bounds of the base type of In_Type. Use Ada_Node for the VC location.

   function Insert_Ref_Context
     (Params     : Transformation_Params;
      Ada_Call   : Node_Id;
      Why_Call   : W_Prog_Id;
      Nb_Of_Refs : Positive;
      Nb_Of_Lets : Natural) return W_Prog_Id;
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

   function Is_Terminal_Node (N : Node_Id) return Boolean;
   --  Decide whether this is a node where we should put a pretty printing
   --  label, or if we should descend further. Basically, everything that's
   --  not a quantifier or conjunction is a terminal node.

   function Needs_Temporary_Ref
     (Actual     : Node_Id;
      Formal     : Node_Id;
      Typ_Formal : W_Type_Id) return Boolean;
   --  True if the parameter passing needs a temporary ref to be performed.

   function New_Assignment
     (Ada_Node : Node_Id := Empty;
      Lvalue   : Node_Id;
      Expr     : W_Prog_Id) return W_Prog_Id;
   --  Translate an assignment of the form "Lvalue := Expr",
   --  using Ada_Node for its source location.

   function New_Predicate_Call
     (Ty     : Entity_Id;
      W_Expr : W_Term_Id;
      Params : Transformation_Params) return W_Pred_Id;
   --  @param Ty type whose predicate needs to be checked
   --  @param W_Expr Why3 expression on which to check the predicate
   --  @param Params transformation parameters
   --  @result Why3 pred that expressed the check

   function New_Predicate_Check
     (Ada_Node : Node_Id;
      Ty       : Entity_Id;
      W_Expr   : W_Expr_Id) return W_Prog_Id;
   --  @param Ada_Node node to which the check is attached
   --  @param Ty type whose predicate needs to be checked
   --  @param W_Expr Why3 expression on which to check the predicate
   --  @result Why3 program that performs the check

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
   --  @param N      the Ada node which defines the component to be updated
   --                  (e.g. a record access)
   --  @param Pref   the currently computed prefix, (e.g. the record value
   --                  before the update)
   --  @param Value  the new value of the updated component
   --  @param Domain the domain
   --  @param Params the translation params
   --  @return the Why expression which corresponds to the Pref object, but
   --            updated at the point specified by N, with value Value

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

   function Transform_Assignment_Statement (Stmt : Node_Id) return W_Prog_Id;
   --  Translate a single Ada statement into a Why expression

   function Transform_Block_Statement (N : Node_Id) return W_Prog_Id;

   function Transform_Concatenation
     (Left               : W_Expr_Id;
      Right              : W_Expr_Id;
      Left_Type          : Entity_Id;
      Right_Type         : Entity_Id;
      Return_Type        : Entity_Id;
      Is_Component_Left  : Boolean;
      Is_Component_Right : Boolean;
      Domain             : EW_Domain;
      Ada_Node           : Node_Id) return W_Expr_Id;
   --  Handle concatenation nodes

   function Transform_Discrete_Choice
     (Choice      : Node_Id;
      Choice_Type : Entity_Id;
      Expr        : W_Expr_Id;
      Domain      : EW_Domain;
      Params      : Transformation_Params) return W_Expr_Id;
   --  For an expression Expr of a discrete type and a discrete Choice, build
   --  the expression that Expr belongs to the range expressed by Choice. In
   --  programs, also generate a check that dynamic choices are in the subtype
   --  Choice_Type.

   function Transform_Declaration (Decl : Node_Id) return W_Prog_Id;
   --  Transform a declaration. Return a program that takes into account the
   --  dynamic semantics of the declaration (checks and assumptions).

   function Transform_Quantified_Expression
     (Expr   : Node_Id;
      Domain : EW_Domain;
      Params : Transformation_Params) return W_Expr_Id;
   --  @return the Why3 expression for SPARK quantified expression [Expr]

   function Transform_Slice
     (Params       : Transformation_Params;
      Domain       : EW_Domain;
      Expr         : Node_Id) return W_Expr_Id;
   --  Transform a slice Expr.

   function Transform_Statement_Or_Declaration
     (Stmt_Or_Decl   : Node_Id;
      Assert_And_Cut : out W_Pred_Id) return W_Prog_Id;
   --  Transform the Ada statement into a Why program expression.
   --  If Assert_And_Cut is not Why_Empty, the statement was a "pragma
   --  Assert_And_Cut". In this case, Assert_And_Cut contains the
   --  Why3 predicate equivalent of the assertion expression, and
   --  Transform_Statement contains the check program expression
   --  that corresponds to the assertion expression.

   function Why_Subp_Has_Precondition
     (E        : Entity_Id;
      Selector : Selection_Kind := Why.Inter.Standard) return Boolean;
   --  Return true whenever the Why declaration that corresponds to the given
   --  subprogram has a precondition.

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
   --  Associations for discriminants are stored before associations for
   --  normal fields.

   function Transform_Function_Call
     (Expr     : Node_Id;
      Domain   : EW_Domain;
      Params   : Transformation_Params) return W_Expr_Id;
   --  Transform a function call

   function Transform_Enum_Literal
     (Expr         : Node_Id;
      Enum         : Entity_Id;
      Domain       : EW_Domain)
      return W_Expr_Id;
   --  Translate an Ada enumeration literal to Why.

   function Transform_Compare_Op
     (Op     : N_Op_Compare;
      Ty     : W_Type_Id;
      Domain : EW_Domain) return W_Identifier_Id;
   --  Convert an Ada comparison operator to a Why relation symbol

   function Transform_Membership_Expression
     (Params : Transformation_Params;
      Domain : EW_Domain;
      Expr   : Node_Id) return W_Expr_Id;
   --  Convert a membership expression (N_In or N_Not_In) into a boolean Why
   --  expression.

   function Transform_Array_Equality
     (Op        : N_Op_Compare;
      Left      : W_Expr_Id;
      Right     : W_Expr_Id;
      Left_Type : Entity_Id;
      Domain    : EW_Domain;
      Ada_Node  : Node_Id) return W_Expr_Id;
   --  Translate an equality on arrays into a Why expression, take care of the
   --  different cases (constrained / unconstrained) for each argument

   function Transform_Array_Comparison
     (Op        : N_Op_Compare;
      Left      : W_Expr_Id;
      Right     : W_Expr_Id;
      Domain    : EW_Domain;
      Ada_Node  : Node_Id) return W_Expr_Id;
   --  Translate a comparison on arrays into a Why expression

   function Transform_Array_Logical_Op
     (Op         : N_Binary_Op;
      Left       : W_Expr_Id;
      Right      : W_Expr_Id;
      Left_Type  : Entity_Id;
      Domain     : EW_Domain;
      Ada_Node   : Node_Id;
      Do_Check   : Boolean) return W_Expr_Id;
   --  Translate a binary operation on boolean arrays into a Why expression

   function Transform_Array_Negation
     (Right      : W_Expr_Id;
      Right_Type : Entity_Id;
      Domain     : EW_Domain;
      Ada_Node   : Node_Id;
      Do_Check   : Boolean) return W_Expr_Id;
   --  Translate negation on boolean arrays into a Why expression

   function Transform_Raise (Stat : Node_Id) return W_Prog_Id with
     Pre => Nkind (Stat) in N_Raise_xxx_Error | N_Raise_Statement;
   --  Returns the Why program for raise statement Stat

   function Transform_Shift_Or_Rotate_Call
     (Expr   : Node_Id;
      Domain : EW_Domain;
      Params : Transformation_Params) return W_Expr_Id;
   --  @param Expr a call where the callee is a shift or rotate subprogram
   --  @param Domain the domain in which the translation happens
   --  @param Params the translation parameters
   --  @return the Why expression corresponding to the shift or rotate

   function Transform_Non_Binary_Modular_Operation
     (Ada_Node   : Node_Id;
      Ada_Type   : Entity_Id;
      Domain     : EW_Domain;
      Op         : N_Op;
      Left_Opnd  : W_Expr_Id := Why_Empty;
      Right_Opnd : W_Expr_Id;
      Rep_Type   : W_Type_Id;
      Modulus    : Uint) return W_Expr_Id
     with Pre => Modulus < UI_Expon (2, 32);
   --  For non binary modular types, it is incorrect to apply the arithmetic
   --  operations - + * on the base type and then apply the modulus on the
   --  result. The special treatment needed in this case is implemented here.
   --
   --  @param Ada_Type type of the Ada node, used to retrieve type Size in bits
   --  @param Op the operation, should be either Minus, Add, Sub or Mul
   --  @param Left_Opnd the left operand of type [Rep_Type], should be empty if
   --     Op is N_Op_Minus.
   --  @param Right_Opnd the right operand of type [Rep_Type]
   --  @param Rep_Type the representation type in which the operation is done.
   --     Both operand should already be converted to this type.
   --  @param Modulus the modulus of the type in which the operation is done.
   --     It should be a non power of two smaller than 2 ** 32.
   --  @return the Why3 expression corresponding to the operation with
   --     modulus applied. One should not call Apply_Modulus_Or_Rounding after
   --     calling this function.

   function Has_Visibility_On_Refined
     (Expr : Node_Id;
      E : Entity_Id)
      return Boolean;
   --  return True if the Expression can "see" the implementation of entity E
   --  (e.g. the Refined_Post, or the full view, etc)

   -------------------
   -- Apply_Modulus --
   -------------------

   function Apply_Modulus_Or_Rounding
     (Op     : N_Op;
      E      : Entity_Id;
      T      : W_Expr_Id;
      Domain : EW_Domain) return W_Expr_Id
   is
      Modulus_Val : Uint;
      BV_Type     : W_Type_Id;

   begin
      if Is_Modular_Integer_Type (E) and then Op /= N_Op_Divide then
         Modulus_Val := Modulus (E);
         BV_Type := Base_Why_Type (E);

         --  If the modulus matches the size of the machine integer (for
         --  example a modulus of 2 ** 32 for a 32-bits machine integer),
         --  no modulo operation is needed.

         if Modulus_Val = UI_Expon (2, Esize (E)) then
            return T;

         --  Otherwise we perform the modulo on bitvectors.

         else
            return New_Call (Name   => MF_BVs (BV_Type).Urem,
                             Domain => Domain,
                             Args   => (1 => T,
                                        2 => New_Modular_Constant
                                               (Value => Modulus_Val,
                                                Typ   => BV_Type)),
                             Typ    => BV_Type);
         end if;

      elsif Is_Floating_Point_Type (E) then
         return New_Call (Domain   => Domain,
                          Name     => E_Symb (E, WNE_Float_Round),
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
      Lvalue : Entity_Id := Defining_Identifier (N);
      Rexpr  : constant Node_Id := Expression (N);
   begin

      --  we ignore part_of objects as a first approximation

      if Is_Part_Of_Protected_Object (Lvalue) then
         return New_Void;
      end if;

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

      --  Some objects have two declarations, i.e. the partial and full view of
      --  a package level object. In this case, we always use the type of the
      --  partial view.

      if Is_Full_View (Lvalue) then
         Lvalue := Partial_View (Lvalue);
      end if;

      if Present (Rexpr) then
         declare
            Binder   : constant Item_Type :=
              Ada_Ent_To_Why.Element (Symbol_Table, Lvalue);
            Why_Ty   : constant W_Type_Id := Type_Of_Node (Etype (Lvalue));
            Why_Expr : constant W_Prog_Id :=
                         +Transform_Expr (Rexpr,
                                          Why_Ty,
                                          EW_Prog,
                                          Params => Body_Params);
            L_Name   : constant String := Full_Name (Lvalue);
         begin
            case Binder.Kind is
            when DRecord =>

               --  For objects in record split form, we produce:
               --  let <v_name>__assume = <init_value> in
               --   <v__fields> := <v_name>__assume.fields;
               --   <v__discrs> := <v_name>__assume.discrs; if discr is mutable
               --   assume (<v__discrs> = <v_name>__assume.discrs); otherwise
               --   assume (<v__constrained>= Is_Constrained (Etype (Lvalue)));
               --   assume (<v__tag> = <v_name>__assume.tag); if classwide
               --   assume (<v__tag> = Ty.__tag); otherwise

               declare
                  Tmp_Var : constant W_Identifier_Id :=
                    New_Identifier (Name => L_Name & "__assume",
                                    Typ  => Why_Ty);
                  Res     : W_Prog_Id := New_Void;
               begin
                  if Binder.Fields.Present then
                     Res := New_Assignment
                       (Ada_Node => N,
                        Name     => Binder.Fields.Binder.B_Name,
                        Value    => +New_Fields_Access (Domain => EW_Prog,
                                                        Name   => +Tmp_Var,
                                                        Ty     => Binder.Typ),
                        Typ      => Get_Typ (Binder.Fields.Binder.B_Name));
                  end if;

                  if Binder.Discrs.Present then
                     if Binder.Discrs.Binder.Mutable then
                        Res := Sequence
                          (Res,
                           New_Assignment
                             (Ada_Node => N,
                              Name     => Binder.Discrs.Binder.B_Name,
                              Value    => +New_Discriminants_Access
                                (Domain => EW_Prog,
                                 Name   => +Tmp_Var,
                                 Ty     => Binder.Typ),
                              Typ      =>
                                Get_Typ (Binder.Discrs.Binder.B_Name)));

                        pragma Assert (Binder.Constr.Present);

                        Res := Sequence
                          (Res,
                           New_Assume_Statement
                           (Ada_Node => N,
                            Pred     =>
                              New_Call
                                (Name => Why_Eq,
                                 Typ => EW_Bool_Type,
                                 Args => (+Binder.Constr.Id, +False_Term))));
                     else
                        Res := Sequence
                          (Res,
                           New_Assume_Statement
                           (Ada_Node => N,
                            Pred     =>
                              New_Call
                                (Name => Why_Eq,
                                 Typ  => EW_Bool_Type,
                                 Args =>
                                   (1 => +Binder.Discrs.Binder.B_Name,
                                    2 =>
                                      New_Discriminants_Access
                                        (Domain => EW_Prog,
                                         Name   => +Tmp_Var,
                                         Ty     => Binder.Typ)))));

                        pragma Assert (not Binder.Constr.Present);
                     end if;
                  end if;

                  if Binder.Tag.Present then
                     Res := Sequence
                       (Res,
                        New_Assume_Statement
                          (Ada_Node => N,
                           Pred     =>
                             New_Call
                               (Name => Why_Eq,
                                Typ  => EW_Bool_Type,
                                Args =>
                                  (1 => +Binder.Tag.Id,
                                   2 =>
                                     (if Is_Class_Wide_Type (Etype (Lvalue))
                                      then New_Tag_Access
                                        (Domain => EW_Prog,
                                         Name   => +Tmp_Var,
                                         Ty     => Binder.Typ)
                                      else +E_Symb (Binder.Typ, WNE_Tag))))));
                  end if;

                  return +New_Typed_Binding
                    (Ada_Node => N,
                     Domain   => EW_Prog,
                     Name     => Tmp_Var,
                     Def      => +Why_Expr,
                     Context  => +Res);
               end;
            when UCArray =>

               --  For objects in array split form, we produce:
               --  let <v_name>__assume = <init_value> in
               --    <v> := of_array (<v_name>__assume);
               --    assume (<v__first> = <v_name>__assume.first);
               --    assume (<v__last> = <v_name>__assume.last);

               declare
                  Tmp_Var : constant W_Identifier_Id :=
                    New_Identifier (Name => L_Name & "__assume",
                                    Typ  => Why_Ty);
                  Res     : W_Prog_Id := New_Assignment
                    (Ada_Node => N,
                     Name     => Binder.Content.B_Name,
                     Value    => +Array_Convert_To_Base (EW_Prog, +Tmp_Var),
                     Typ      => Get_Typ (Binder.Content.B_Name));
               begin
                  for I in 1 .. Binder.Dim loop
                     Res := Sequence
                       ((1 => Res,
                         2 => New_Assume_Statement
                           (Ada_Node => N,
                            Pred     =>
                              New_Call
                                (Name => Why_Eq,
                                 Typ  => EW_Bool_Type,
                                 Args =>
                                   (1 => Insert_Conversion_To_Rep_No_Bool
                                      (EW_Prog,
                                       +Binder.Bounds (I).First),
                                    2 => Insert_Conversion_To_Rep_No_Bool
                                      (EW_Prog,
                                       +Get_Array_Attr
                                         (Domain => EW_Prog,
                                          Expr   => +Tmp_Var,
                                          Attr   => Attribute_First,
                                          Dim    => I))))),
                         3 => New_Assume_Statement
                           (Ada_Node => N,
                            Pred     =>
                              New_Call
                                (Name => Why_Eq,
                                 Typ  => EW_Bool_Type,
                                 Args =>
                                   (1 => Insert_Conversion_To_Rep_No_Bool
                                      (EW_Prog,
                                       +Binder.Bounds (I).Last),
                                    2 => Insert_Conversion_To_Rep_No_Bool
                                      (EW_Prog,
                                       +Get_Array_Attr
                                         (Domain => EW_Prog,
                                          Expr   => +Tmp_Var,
                                          Attr   => Attribute_Last,
                                          Dim    => I)))))));
                  end loop;

                  return +New_Typed_Binding
                    (Ada_Node => N,
                     Domain   => EW_Prog,
                     Name     => Tmp_Var,
                     Def      => +Why_Expr,
                     Context  => +Res);
               end;
            when Regular | Prot_Self =>
               declare
                  L_Id     : constant W_Identifier_Id :=
                    To_Why_Id (Lvalue, Typ => Why_Ty);
               begin
                  if Is_Mutable_In_Why (Lvalue) then

                     --  Attributes of record objects have the default values
                     --  of their type

                     return New_Assignment
                       (Ada_Node => N,
                        Name     => L_Id,
                        Value    =>
                          (if Has_Record_Type (Etype (Lvalue))
                           or else Full_View_Not_In_SPARK (Etype (Lvalue))
                           then +New_Record_Attributes_Update
                             (Ada_Node => N,
                              Domain   => EW_Prog,
                              Name     => +Why_Expr,
                              Ty       => Etype (Lvalue))
                           else Why_Expr),
                          Typ    => Why_Ty);

                  elsif Is_Static_Expression (Rexpr) then

                     --  We generate an ignore statement, to obtain all the
                     --  checks
                     --  ??? Is this necessary? after all, we would get a
                     --  compiler warning anyway

                     return New_Ignore (Prog => Why_Expr);

                  else
                     declare
                        Tmp_Var : constant W_Identifier_Id :=
                          New_Identifier (Name => L_Name & "__assume",
                                          Typ  => Why_Ty);
                        Eq      : constant W_Pred_Id :=
                          New_Call
                            (Name => Why_Eq,
                             Typ  => EW_Bool_Type,
                             Args => (New_Record_Attributes_Update
                                      (Ada_Node => N,
                                       Domain   => EW_Prog,
                                       Name     => +Tmp_Var,
                                       Ty       => Etype (Lvalue)),
                                      +L_Id));
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
                              Pred     => Eq));
                     end;
                  end if;
               end;
            when Func =>
               raise Program_Error;
            end case;
         end;

      elsif not Is_Partial_View (Defining_Identifier (N))
        and then not Is_Imported (Lvalue)
      then

         --  Only assume default initialization if we are in a fullview.

         pragma Assert (Is_Mutable_In_Why (Lvalue));

         --  Constants cannot be default initialized.

         declare
            Binder          : constant Item_Type :=
              Ada_Ent_To_Why.Element (Symbol_Table, Lvalue);
            L_Deref         : constant W_Expr_Id :=
              Reconstruct_Item (Binder, Ref_Allowed => True);

            Constrained_Ty  : constant Entity_Id :=
              Etype (Defining_Identifier (N));
            --  Type of the fullview

            Default_Checks  : W_Prog_Id :=
              Compute_Default_Check (Constrained_Ty, Body_Params);
            --  Checks for runtime errors in default values

            Init_Assumption : constant W_Pred_Id :=
              Compute_Default_Init
                (Expr   => Insert_Simple_Conversion
                   (Ada_Node => Lvalue,
                    Domain   => EW_Pred,
                    Expr     => L_Deref,
                    To       => Type_Of_Node (Constrained_Ty)),
                 Ty     => Constrained_Ty);
            --  Assume initial value of L
         begin

            --  Generate assumption

            if Default_Checks /= New_Void then
               Default_Checks := +New_Ignore
                 (Ada_Node => Lvalue,
                  Prog     => Default_Checks);
            end if;

            if Init_Assumption = True_Pred then
               return Default_Checks;
            else
               return Sequence
                 (Left  => +New_Ignore
                    (Ada_Node => Lvalue,
                     Prog     => Default_Checks),
                  Right => New_Assume_Statement
                    (Ada_Node    => N,
                     Pred        => Init_Assumption));
            end if;
         end;
      else
         return New_Void;
      end if;
   end Assignment_Of_Obj_Decl;

   ----------------------------------
   -- Assume_Declaration_Of_Entity --
   ----------------------------------

   procedure Assume_Declaration_Of_Entity
     (E             : Entity_Id;
      Params        : Transformation_Params;
      Initialized   : Boolean;
      Top_Predicate : Boolean;
      Context       : in out W_Prog_Id)
   is
      Max_Assocs : constant Natural := 100;
      --  if the defining expression of a constant contains more than
      --  Max_Assocs N_Component_Association nodes, its definition will not be
      --  inlined.

      L_Id : constant W_Expr_Id :=
        Transform_Identifier (Params   => Params,
                              Expr     => E,
                              Ent      => E,
                              Domain   => EW_Term);

   begin
      --  Assume dynamic property of E

         Context := Sequence
           (Context,
            Assume_Dynamic_Invariant
              (Expr          => +L_Id,
               Ty            => Etype (E),
               Initialized   => Initialized,
               Only_Var      => False,
               Top_Predicate => Top_Predicate));

      --  Assume value if constant

      if (Is_Object (E) and then Ekind (E) = E_Constant)
        or else Is_Named_Number (E)
      then
         declare
            Typ  : constant W_Type_Id := Why_Type_Of_Entity (E);
            FV   : constant Entity_Id :=
              (if Is_Object (E) and then Is_Partial_View (E)
               and then Entity_In_SPARK (Full_View (E))
               then Full_View (E) else E);
            Decl : constant Node_Id := Parent (FV);
            Expr : W_Expr_Id;
         begin
            if Ekind (FV) /= E_In_Parameter
              and then Present (Expression (Decl))
              and then Comes_From_Source (FV)
              and then Number_Of_Assocs_In_Expression
                (Expression (Decl)) <= Max_Assocs
            then

               --  We do not issue checks here. Checks for this
               --  declaration will be issued when verifying its
               --  enclosing unit.

               Expr :=
                 +Transform_Expr (Expression (Decl),
                                  Typ,
                                  EW_Pterm,
                                  Params => Body_Params);
               declare
                  Tmp_Var : constant W_Identifier_Id :=
                    New_Temp_Identifier (Typ => Typ);
                  Eq      : constant W_Pred_Id :=
                    New_Call
                      (Name => Why_Eq,
                       Typ  => EW_Bool_Type,
                       Args =>
                         ((if Has_Record_Type (Etype (E))
                          or else Full_View_Not_In_SPARK
                            (Etype (E))
                          then
                             New_Record_Attributes_Update
                            (Domain   => EW_Prog,
                             Name     => +Tmp_Var,
                             Ty       => Etype (E))
                          else +Tmp_Var),
                          +L_Id));
               begin
                  if not Has_Dereference (+Expr) then
                     Context := Sequence
                       (Context,
                        +New_Typed_Binding
                          (Domain   => EW_Prog,
                           Name     => Tmp_Var,
                           Def      => +Expr,
                           Context  =>
                             +New_Assume_Statement (Pred => Eq)));
                  end if;
               end;
            end if;
         end;
      end if;
   end Assume_Declaration_Of_Entity;

   ------------------------------
   -- Assume_Dynamic_Invariant --
   ------------------------------

   function Assume_Dynamic_Invariant
     (Expr          : W_Term_Id;
      Ty            : Entity_Id;
      Initialized   : Boolean := True;
      Only_Var      : Boolean := True;
      Top_Predicate : Boolean := True;
      Use_Pred      : Boolean := True) return W_Prog_Id
   is
      Init     : constant W_Term_Id :=
        (if Initialized then True_Term else False_Term);
      O_Var    : constant W_Term_Id :=
        (if Only_Var then True_Term else False_Term);
      Top_Pred : constant W_Term_Id :=
        (if Top_Predicate then True_Term else False_Term);
      T        : constant W_Pred_Id :=
        Compute_Dynamic_Invariant (Expr          => Expr,
                                  Ty            => Ty,
                                  Initialized   => Init,
                                  Only_Var      => O_Var,
                                  Top_Predicate => Top_Pred,
                                  Use_Pred      => Use_Pred);
   begin
      if T /= True_Pred then
         return New_Assume_Statement (Ada_Node => Ty,
                                      Pred     => T);
      else
         return New_Void;
      end if;
   end Assume_Dynamic_Invariant;

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
      --  If N is inside the consequence expression of a contract case, return
      --  the corresponding guard expression. Otherwise, return Empty.

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
            Is_Pragma_Check (P, Name_Refined_Post)
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

   --  Start of processing for Bind_From_Mapping_In_Expr

   begin
      for C in Map.Iterate loop
         declare
            N     : constant Node_Id := Ada_To_Why_Ident.Key (C);
            Name  : constant W_Identifier_Id := Ada_To_Why_Ident.Element (C);
            Guard : constant Node_Id :=
              (if Bind_Value_Of_Old
               then Get_Corresponding_Guard (N)
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
                      New_Call
                        (Name   => Why_Eq,
                         Typ    => EW_Bool_Type,
                         Args =>
                           (1 => +New_Result_Ident (EW_Abstract (Etype (N))),
                            2 => +Transform_Expr (N, EW_Term, Params)))),
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
        (if Domain = EW_Term then EW_Pred
         elsif Domain = EW_Prog then EW_Pterm
         else Domain);
      --  As the choices must be static, we do not need to generate checks
      --  for them.

      Cases        : constant List_Id := Alternatives (N);
      First_Case   : constant Node_Id := First (Cases);
      Last_Case    : constant Node_Id := Last (Cases);
      Expr         : constant Node_Id := Expression (N);
      Cur_Case     : Node_Id;
      Matched_Expr : constant W_Expr_Id :=
                       Transform_Expr (Expr,
                                       Base_Why_Type_No_Bool
                                         (Entity_Id'(Type_Of_Node (Expr))),
                                       Match_Domain,
                                       Params);
      Then_Expr    : constant W_Expr_Id := Branch_Expr (First_Case);
      Elsif_Parts  : W_Expr_Array (1 .. Integer (List_Length (Cases)) - 2);

   --  Start of processing for Case_Expr_Of_Ada_Node

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
                      Choice_Type  => Empty,
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
                 Choice_Type  => Empty,
                 Matched_Expr => Matched_Expr,
                 Cond_Domain  => Cond_Domain,
                 Params       => Params),
            Then_Part   => Then_Expr,
            Elsif_Parts => Elsif_Parts,
            Else_Part   => Branch_Expr (Last_Case),
            Typ         => Get_Type (Then_Expr));
      end if;
   end Case_Expr_Of_Ada_Node;

   ------------------------
   -- Check_Scalar_Range --
   ------------------------

   function Check_Scalar_Range
     (Params : Transformation_Params;
      N      : Entity_Id;
      Base   : Entity_Id) return W_Prog_Id
   is
   begin
      --  If either the base type or the range is not static, we need to
      --  generate a check that the subtype declaration is valid; otherwise,
      --  the frontend has done it for us already.

      if Is_OK_Static_Range (Get_Range (N))
        and then (No (Base) or else Has_Static_Scalar_Subtype (Base))
      then
         return New_Void;
      else
         pragma Assert (Present (Base));
         declare
            Rng              : constant Node_Id := Get_Range (N);
            Why_Base         : constant W_Type_Id := Base_Why_Type (Base);
            Le               : constant W_Identifier_Id :=
              (if Why_Base = EW_Real_Type then Real_Infix_Le
               elsif Why_Type_Is_BitVector (Why_Base) then
                    MF_BVs (Why_Base).Ule
               else Int_Infix_Le);
            Low_Expr         : constant W_Term_Id :=
              +Transform_Expr (Low_Bound (Rng), Why_Base, EW_Term, Params);
            High_Expr        : constant W_Term_Id :=
              +Transform_Expr (High_Bound (Rng), Why_Base, EW_Term, Params);
            First_In_Range   : constant W_Pred_Id :=
              New_Call
                (Name =>
                   (if Why_Base = EW_Real_Type then Real_Infix_Ge
                    elsif Why_Type_Is_BitVector (Why_Base) then
                      MF_BVs (Why_Base).Uge
                    else Int_Infix_Ge),
                 Typ  => EW_Bool_Type,
                 Args => (+Low_Expr,
                          +New_Attribute_Expr
                            (Base, EW_Term, Attribute_First, Params)));
            Last_In_Range    : constant W_Pred_Id :=
              New_Call
                (Name => Le,
                 Typ  => EW_Bool_Type,
                 Args => (+High_Expr,
                             +New_Attribute_Expr
                               (Base, EW_Term, Attribute_Last, Params)));
            First_Le_Last    : constant W_Pred_Id :=
              New_Call
                (Name => Le,
                 Typ  => EW_Bool_Type,
                 Args => (+Low_Expr, +High_Expr));
            Precond          : constant W_Pred_Id :=
              +New_Connection
              (Op     => EW_Imply,
               Left   => +First_Le_Last,
               Right  =>
                 +New_And_Expr
                 (Domain => EW_Pred,
                  Left   => +First_In_Range,
                  Right => +Last_In_Range));

            Check_Range      : W_Prog_Id;
         begin

            --  We need to check both that the range is OK (either
            --  empty or contained in the range's type) and that there cannot
            --  be any runtime errors during the computation of the bounds.
            --  If the range bounds where computed by the frontend, we assume
            --  that they are correct.

            Check_Range :=
              +New_VC_Expr (Ada_Node => N,
                            Domain   => EW_Prog,
                            Reason   => VC_Range_Check,
                            Expr     =>
                              +New_Any_Statement (Ada_Node => N,
                                                  Pre      => Precond,
                                                  Post     => True_Pred));

            if Comes_From_Source (Low_Bound (Rng))
              and then not Is_OK_Static_Expression (Low_Bound (Rng))
            then
               Check_Range := Sequence
                 (New_Ignore
                    (Ada_Node => N,
                     Prog     => +Transform_Expr
                       (Low_Bound (Rng), Why_Base, EW_Prog, Params)),
                  Check_Range);
            end if;

            if Comes_From_Source (High_Bound (Rng))
              and then not Is_OK_Static_Expression (High_Bound (Rng))
            then
               Check_Range := Sequence
                 (New_Ignore
                    (Ada_Node => N,
                     Prog     => +Transform_Expr
                       (High_Bound (Rng), Why_Base, EW_Prog, Params)),
                  Check_Range);
            end if;

            return Check_Range;
         end;
      end if;
   end Check_Scalar_Range;

   ------------------------------
   -- Check_Subtype_Indication --
   ------------------------------

   function Check_Subtype_Indication
     (Params   : Transformation_Params;
      N        : Node_Id;
      Sub_Type : Entity_Id) return W_Prog_Id is
   begin
      if Is_Scalar_Type (Sub_Type) then
         return Check_Scalar_Range (Params   => Params,
                                    N        => Sub_Type,
                                    Base     => Etype (Subtype_Mark (N)));
      else
         return New_Void;
      end if;
   end Check_Subtype_Indication;

   ----------------------------------
   -- Compute_Attach_Handler_Check --
   ----------------------------------

   function Compute_Attach_Handler_Check
     (Ty     : Entity_Id;
      Params : Transformation_Params) return W_Prog_Id
   is
      function Single_Attach_Handler_Check (Proc : Entity_Id) return W_Prog_Id;
      --  @param Proc a procedure with an attach_handler pragma
      --  @return an assertion statement that expresses the attach handler
      --    check for this pragma

      ---------------------------------
      -- Single_Attach_Handler_Check --
      ---------------------------------

      function Single_Attach_Handler_Check (Proc : Entity_Id) return W_Prog_Id
      is

         --  the interrupt is given as the second argument of the pragma
         --  Attach_Handler
         Att_Val : constant Node_Id :=
           Expression (Next (First (Pragma_Argument_Associations
                       (Get_Pragma (Proc, Pragma_Attach_Handler)))));

         --  to check whether the attach handler is reserved, we call the
         --  Ada.Interrupts.Is_Reserved. However, this function reads a global
         --  state, which makes it a bit difficult to generate a call in
         --  the logic (we would have to come up with the state object - not
         --  impossible but not currently proposed by frontend). Instead,
         --  we call the program function, which has only the interrupt as
         --  argument, store the result in a temp and assert that the result
         --  is false. So we are essentially asserting "not is_reserved(int)".

         Res     : constant W_Expr_Id :=
           New_Temp_For_Expr
             (New_Call
                (Name   => To_Why_Id (RTE (RE_Is_Reserved), Domain => EW_Prog),
                 Domain => EW_Prog,
                 Args   =>
                   (1 =>
                       Transform_Expr (Att_Val, EW_Int_Type, EW_Term, Params)),
                 Typ    => EW_Bool_Type));
         Pred    : constant W_Pred_Id :=
           New_Call
             (Name => Why_Eq,
              Args => (1 => +Res,
                       2 => Bool_False (EW_Term)));
      begin
         return
           +Binding_For_Temp
             (Domain  => EW_Prog,
              Tmp     => Res,
              Context =>
                +New_Located_Assert
                  (Ada_Node => Att_Val,
                   Reason   => VC_Interrupt_Reserved,
                   Kind     => EW_Check,
                   Pred     => Pred));
      end Single_Attach_Handler_Check;

      Proc : Node_Id :=
        First (Visible_Declarations (Protected_Definition (Parent (Ty))));
      Stat : W_Prog_Id := New_Void;

      --  Start of processing for Compute_Attach_Handler_Check

   begin
      while Present (Proc) loop
         if Nkind (Proc) = N_Subprogram_Declaration then
            declare
               Ent : constant Entity_Id := Defining_Entity (Proc);
            begin
               if Ekind (Ent) = E_Procedure
                 and Get_Pragma (Ent, Pragma_Attach_Handler) /= Empty
               then
                  Stat := Sequence (Stat,
                                    Single_Attach_Handler_Check (Ent));
               end if;
            end;
         end if;
         Next (Proc);
      end loop;
      return Stat;
   end Compute_Attach_Handler_Check;

   -----------------------
   -- Compute_Call_Args --
   -----------------------

   function Compute_Call_Args
     (Call        :     Node_Id;
      Domain      :     EW_Domain;
      Nb_Of_Refs  : out Natural;
      Nb_Of_Lets  : out Natural;
      Params      :     Transformation_Params) return W_Expr_Array
   is
      Subp    : constant Entity_Id := Get_Called_Entity (Call);
      Binders : constant Item_Array :=
        Compute_Subprogram_Parameters (Subp, Domain);

   begin
      Nb_Of_Refs := 0;
      Nb_Of_Lets := 0;

      if Binders'Length = 0 then
         return (1 => New_Void (Call));
      end if;

      declare
         Why_Args : W_Expr_Array (1 .. Item_Array_Length (Binders));
         Arg_Cnt  : Positive := 1;
         Bind_Cnt : Positive := Binders'First;

         procedure Compute_Arg (Formal, Actual : Node_Id);
         --  Compute a Why expression for each parameter

         -----------------
         -- Compute_Arg --
         -----------------

         procedure Compute_Arg (Formal, Actual : Node_Id) is
         begin
            case Binders (Bind_Cnt).Kind is
               when Regular =>

                  --  If a conversion or a component indexing is needed,
                  --  it can only be done for a value. That is to say,
                  --  something of this sort should be generated:
                  --
                  --  let formal = ref to_formal (!actual) in
                  --   (subprogram_call (formal); actual := !formal)
                  --
                  --  The generation of the context is left to the
                  --  caller; this function only signals the existence of
                  --  such parameters by incrementing Nb_Of_Refs.

                  if Needs_Temporary_Ref (Actual, Formal,
                                          Get_Typ
                                            (Binders (Bind_Cnt).Main.B_Name))
                  then
                     --  We should never use the Formal for the Ada_Node,
                     --  because there is no real dependency here; We only
                     --  use the Formal to get a sensible name.

                     Why_Args (Arg_Cnt) :=
                       +New_Identifier (Ada_Node => Empty,
                                        Name     => Full_Name (Formal),
                                        Typ      =>
                                          Get_Typ
                                            (Binders (Bind_Cnt).Main.B_Name));
                     Nb_Of_Refs := Nb_Of_Refs + 1;

                  else
                     case Ekind (Formal) is
                     when E_In_Out_Parameter | E_Out_Parameter =>
                        pragma Assert
                          (Ada_Ent_To_Why.Element
                             (Symbol_Table, Entity (Actual)).Kind = Regular);

                        --  Parameters that are "out" are refs;
                        --  if the actual is a simple identifier and no
                        --  conversion is needed, it can be translated "as is".

                        Why_Args (Arg_Cnt) :=
                          +Ada_Ent_To_Why.Element
                            (Symbol_Table, Entity (Actual)).Main.B_Name;

                     when others =>

                        --  When the formal is an "in" scalar, we actually use
                        --  "int" as a type.

                        Why_Args (Arg_Cnt) :=
                          Transform_Expr
                            (Actual,
                             Get_Typ (Binders (Bind_Cnt).Main.B_Name),
                             Domain,
                             Params);
                     end case;
                  end if;
                  Arg_Cnt := Arg_Cnt + 1;

               when Prot_Self =>

                  declare
                     Prot : constant W_Identifier_Id :=
                       Binders (Bind_Cnt).Main.B_Name;
                  begin
                     --  external call, pass the object itself

                     if Nkind (Sinfo.Name (Call)) = N_Selected_Component then
                        Why_Args (Arg_Cnt) :=
                          Transform_Expr
                            (Prefix (Sinfo.Name (Call)),
                             Get_Typ (Prot),
                             Domain,
                             Params);
                     elsif Self_Is_Mutable then
                        Why_Args (Arg_Cnt) :=
                          New_Deref (Right => Prot,
                                     Typ   => Get_Typ (Prot));
                     else
                        Why_Args (Arg_Cnt) := +Prot;
                     end if;
                  end;

                  Arg_Cnt := Arg_Cnt + 1;

               when DRecord =>
                  pragma Assert (Ekind (Formal) in
                                   E_In_Out_Parameter | E_Out_Parameter);

                  declare
                     Formal_Binder : constant Item_Type :=
                       Binders (Bind_Cnt);
                  begin

                     --  The actual is in split form iff it is an identifier.

                     if Nkind (Actual) in N_Identifier | N_Expanded_Name then
                        declare
                           Actual_Binder : constant Item_Type :=
                             Ada_Ent_To_Why.Element
                               (Symbol_Table, Entity (Actual));
                        begin
                           pragma Assert (Actual_Binder.Kind = DRecord);

                           --  If the formal and the actual do not have exactly
                           --  the same type, we need a temporary variable to
                           --  hold the result of the conversion.

                           if not Eq_Base
                             (EW_Abstract (Binders (Bind_Cnt).Typ),
                              EW_Abstract (Actual_Binder.Typ))
                           then
                              Nb_Of_Lets := Nb_Of_Lets + 1;
                           end if;

                           if Formal_Binder.Fields.Present
                             and then Actual_Binder.Fields.Present
                             and then
                               Eq_Base (EW_Abstract (Binders (Bind_Cnt).Typ),
                                        EW_Abstract (Actual_Binder.Typ))
                           then

                              --  If the actual is in split form and as the
                              --  same type as the formal, then the field
                              --  reference can be used as is.

                              Why_Args (Arg_Cnt) :=
                                +Actual_Binder.Fields.Binder.B_Name;

                              Arg_Cnt := Arg_Cnt + 1;
                           elsif Formal_Binder.Fields.Present then

                              --  Otherwise, we need a new reference.

                              Why_Args (Arg_Cnt) :=
                                +New_Identifier
                                (Ada_Node => Empty,
                                 Name     => Full_Name (Formal) & "__fields",
                                 Typ      =>
                                   Get_Typ
                                     (Formal_Binder.Fields.Binder.B_Name));

                              Nb_Of_Refs := Nb_Of_Refs + 1;

                              Arg_Cnt := Arg_Cnt + 1;
                           end if;

                           if Formal_Binder.Discrs.Present
                             and then Formal_Binder.Discrs.Binder.Mutable
                             and then Actual_Binder.Discrs.Binder.Mutable
                           then

                              --  If the formal has mutable discriminants, the
                              --  actual is in split form and has mutable
                              --  discrimiants, the discriminant reference can
                              --  be used as is.

                              Why_Args (Arg_Cnt) :=
                                +Actual_Binder.Discrs.Binder.B_Name;

                              Arg_Cnt := Arg_Cnt + 1;
                           elsif Formal_Binder.Discrs.Present
                             and then Formal_Binder.Discrs.Binder.Mutable
                           then

                              --  If the formal is mutable and not the actual,
                              --  we need a new reference.

                              Why_Args (Arg_Cnt) :=
                                +New_Identifier
                                (Ada_Node => Empty,
                                 Name     => Full_Name (Formal) & "__discrs",
                                 Typ      =>
                                   Get_Typ
                                     (Formal_Binder.Discrs.Binder.B_Name));

                              Nb_Of_Refs := Nb_Of_Refs + 1;

                              Arg_Cnt := Arg_Cnt + 1;

                           elsif Formal_Binder.Discrs.Present then
                              pragma Assert (Actual_Binder.Discrs.Present);

                              Why_Args (Arg_Cnt) :=
                                (if Actual_Binder.Discrs.Binder.Mutable then
                                    New_Deref
                                   (Right =>
                                        Actual_Binder.Discrs.Binder.B_Name,
                                    Typ   => Get_Typ
                                      (Actual_Binder.Discrs.Binder.B_Name))
                                 else +Actual_Binder.Discrs.Binder.B_Name);

                              Arg_Cnt := Arg_Cnt + 1;
                           end if;

                           if Formal_Binder.Constr.Present then

                              Why_Args (Arg_Cnt) :=
                                (if Actual_Binder.Constr.Present then
                                 +Actual_Binder.Constr.Id
                                 else +True_Prog);

                              Arg_Cnt := Arg_Cnt + 1;
                           end if;

                           if Formal_Binder.Tag.Present then
                              pragma Assert (Actual_Binder.Tag.Present);

                              Why_Args (Arg_Cnt) := +Actual_Binder.Tag.Id;

                              Arg_Cnt := Arg_Cnt + 1;
                           end if;
                        end;

                     else
                        --  We use a temporary variable to avoid recomputing
                        --  the actual several times.

                        Nb_Of_Lets := Nb_Of_Lets + 1;

                        declare
                           Tmp_Actual    : constant W_Expr_Id :=
                             +New_Identifier
                             (Name   => Full_Name (Formal) & "__compl",
                              Domain => EW_Term,
                              Typ    => EW_Abstract (Formal_Binder.Typ));
                        begin

                           if Formal_Binder.Fields.Present then

                              --  We need a new reference.

                              Why_Args (Arg_Cnt) :=
                                +New_Identifier
                                (Ada_Node => Empty,
                                 Name     => Full_Name (Formal) & "__fields",
                                 Typ      =>
                                   Get_Typ
                                     (Formal_Binder.Fields.Binder.B_Name));

                              Nb_Of_Refs := Nb_Of_Refs + 1;

                              Arg_Cnt := Arg_Cnt + 1;
                           end if;

                           if Formal_Binder.Discrs.Present
                             and then Formal_Binder.Discrs.Binder.Mutable
                           then

                              --  If the formal is mutable, we need a new
                              --  reference.

                              Why_Args (Arg_Cnt) :=
                                +New_Identifier
                                (Ada_Node => Empty,
                                 Name     => Full_Name (Formal) & "__discrs",
                                 Typ      =>
                                   Get_Typ
                                     (Formal_Binder.Discrs.Binder.B_Name));

                              Nb_Of_Refs := Nb_Of_Refs + 1;

                              Arg_Cnt := Arg_Cnt + 1;

                           elsif Formal_Binder.Discrs.Present then

                              Why_Args (Arg_Cnt) :=
                                New_Discriminants_Access
                                  (Ada_Node => Actual,
                                   Domain   => EW_Prog,
                                   Name     => Tmp_Actual,
                                   Ty       => Formal_Binder.Typ);

                              Arg_Cnt := Arg_Cnt + 1;
                           end if;

                           if Formal_Binder.Constr.Present then
                              Why_Args (Arg_Cnt) :=
                                New_Is_Constrained_Access
                                  (Ada_Node => Actual,
                                   Domain   => EW_Prog,
                                   Name     => Tmp_Actual,
                                   Ty       => Formal_Binder.Typ);

                              Arg_Cnt := Arg_Cnt + 1;
                           end if;

                           if Formal_Binder.Tag.Present then
                              Why_Args (Arg_Cnt) :=
                                New_Tag_Access
                                  (Ada_Node => Actual,
                                   Domain   => EW_Prog,
                                   Name     => Tmp_Actual,
                                   Ty       => Formal_Binder.Typ);

                              Arg_Cnt := Arg_Cnt + 1;
                           end if;
                        end;
                     end if;
                  end;

               when UCArray =>
                  pragma Assert (Ekind (Formal) in
                                   E_In_Out_Parameter | E_Out_Parameter);

                  --  If the actual is not in split form, we use a
                  --  temporary variable for it to avoid computing it
                  --  multiple times.

                  declare
                     Actual_Type : constant W_Type_Id :=
                       Type_Of_Node (Actual);
                     Array_Expr  : constant W_Expr_Id :=
                       (if Get_Type_Kind (Actual_Type) = EW_Abstract then
                        +New_Identifier
                          (Ada_Node => Empty,
                           Name     => Full_Name (Formal) & "__compl",
                           Typ      => Actual_Type)
                        else Transform_Expr (Actual, Domain, Params));
                     Need_Ref : constant Boolean :=
                       Get_Type_Kind (Actual_Type) = EW_Abstract
                       or else not (Nkind (Actual) in N_Identifier |
                                    N_Expanded_Name);
                  begin
                     if Need_Ref then
                        if Get_Type_Kind (Actual_Type) = EW_Abstract then

                           --  The actual is not in split form. We need a
                           --  temporary variable for the content of the array.

                           Nb_Of_Lets := Nb_Of_Lets + 1;
                        end if;

                        Why_Args (Arg_Cnt) :=
                          +New_Identifier
                          (Ada_Node => Empty,
                           Name     => Full_Name (Formal),
                           Typ      =>
                             Get_Typ (Binders (Bind_Cnt).Content.B_Name));
                        Nb_Of_Refs := Nb_Of_Refs + 1;
                     else

                        --  If the actual is an entity in split form, it can
                        --  be used as is.

                        Why_Args (Arg_Cnt) :=
                          +Ada_Ent_To_Why.Element
                            (Symbol_Table, Entity (Actual)).Content.B_Name;
                     end if;

                     Arg_Cnt := Arg_Cnt + 1;

                     --  If the binder is an unconstrained array in split form,
                     --  we need to give arguments for its bounds.
                     --  Since these bounds are integer constants, they don't
                     --  need a temporary variable and are translated as is.

                     for I in 1 .. Binders (Bind_Cnt).Dim loop
                        Why_Args (Arg_Cnt) :=
                          Insert_Simple_Conversion
                            (Domain   => Domain,
                             Expr     => Get_Array_Attr (Domain => Domain,
                                             Expr   => Array_Expr,
                                             Attr   => Attribute_First,
                                             Dim    => I),
                             To       =>
                               Get_Typ (Binders (Bind_Cnt).Bounds (I).First));
                        Why_Args (Arg_Cnt + 1) :=
                          Insert_Simple_Conversion
                            (Domain   => Domain,
                             Expr     => Get_Array_Attr (Domain => Domain,
                                             Expr   => Array_Expr,
                                             Attr   => Attribute_Last,
                                             Dim    => I),
                             To       =>
                               Get_Typ (Binders (Bind_Cnt).Bounds (I).Last));
                        Arg_Cnt := Arg_Cnt + 2;
                     end loop;
                  end;
               when Func    =>
                  raise Program_Error;
            end case;

            Bind_Cnt := Bind_Cnt + 1;
         end Compute_Arg;

         procedure Iterate_Call is new
           Iterate_Call_Arguments (Compute_Arg);
      begin

         --  In the case of protected subprograms, there is an invisible first
         --  parameter, the protected object itself. We call "Compute_Arg" with
         --  empty arguments to process this case.

         if Is_Protected_Subprogram (Subp) then
            Compute_Arg (Empty, Empty);
         end if;

         Iterate_Call (Call);

         --  Loop over remaining logical binders

         for B in Bind_Cnt .. Binders'Last loop
            pragma Assert (Binders (B).Kind in Regular);
            Why_Args (Arg_Cnt) :=
              Get_Logic_Arg (Binders (B).Main, Params.Ref_Allowed);
            Arg_Cnt := Arg_Cnt + 1;
         end loop;

         --  We also need to add inclusions to allow the usage of those read
         --  variables

         Add_Dependencies_For_Effects (Params.Theory, Subp);

         return Why_Args;
      end;
   end Compute_Call_Args;

   ---------------------------
   -- Compute_Default_Check --
   ---------------------------

   function Compute_Default_Check
     (Ty     : Entity_Id;
      Params : Transformation_Params) return W_Prog_Id is

      --  If Ty's fullview is in SPARK, go to its underlying type to check its
      --  kind.

      Ty_Ext : constant Entity_Id := Retysp (Ty);
      Checks : W_Prog_Id := New_Void;
   begin
      if Is_Scalar_Type (Ty_Ext) then
         if Has_Default_Aspect (Ty_Ext) then
            declare
               Default_Expr : constant W_Expr_Id :=
                 Transform_Expr
                      (Expr          => Default_Aspect_Value (Ty_Ext),
                       Expected_Type => Base_Why_Type (Ty_Ext),
                       Domain        => EW_Prog,
                       Params        => Params);
               Range_Check  : constant W_Expr_Id :=
                 Insert_Scalar_Conversion
                   (Domain     => EW_Prog,
                    Ada_Node   => Default_Aspect_Value (Ty_Ext),
                    Expr       => Default_Expr,
                    To         => Type_Of_Node (Ty_Ext),
                    Range_Type => Ty_Ext,
                    Check_Kind => RCK_Range);
            begin
               Checks := +Range_Check;
            end;
         end if;
      elsif Is_Array_Type (Ty_Ext)
        and then Ekind (Ty_Ext) /= E_String_Literal_Subtype
      then
         pragma Assert (Is_Constrained (Ty_Ext));

         --  Generates:
         --  length (Index_Type1) > 0 /\ .. ->
         --    Default_Component_Value         <if any>
         --    default_checks (Component_Type) <otherwise>

         declare
            Range_Expr : W_Prog_Id := True_Prog;
            Num_Dim    : constant Positive :=
              Positive (Number_Dimensions (Ty_Ext));
            T_Comp     : W_Expr_Id;
         begin

            --  Generate the condition length (Index_Type1) > 0 /\ ..

            for Dim in 1 .. Num_Dim loop
               Range_Expr := +New_And_Expr
                 (Left   => +Range_Expr,
                  Right  => New_Comparison
                    (Symbol => Int_Infix_Gt,
                     Left   => Build_Length_Expr
                       (Domain => EW_Prog,
                        Ty     => Ty_Ext,
                        Dim    => Dim),
                     Right  => New_Integer_Constant (Empty, Uint_0),
                     Domain => EW_Prog),
                  Domain => EW_Prog);
            end loop;

            --  Generate the check for the default value of Component_Type
            --    Default_Component_Value         <if any>
            --    default_checks (Component_Type) <otherwise>

            if Has_Default_Aspect (Ty_Ext) then

               --  if Ty_Ext as a Default_Component_Value aspect, use it.

               T_Comp := Transform_Expr
                 (Expr          => Default_Aspect_Component_Value (Ty_Ext),
                  Expected_Type => Type_Of_Node (Component_Type (Ty_Ext)),
                  Domain        => EW_Prog,
                  Params        => Params);
            else

               --  otherwise, use its Component_Type default value.

               T_Comp := +Compute_Default_Check
                 (Ty     => Component_Type (Ty_Ext),
                  Params => Params);
            end if;

            if T_Comp /= New_Void then
               T_Comp := New_Conditional
                 (Ada_Node    => Ty,
                  Domain      => EW_Prog,
                  Condition   => +Range_Expr,
                  Then_Part   => +New_Ignore
                    (Component_Type (Ty_Ext), +T_Comp));

               Checks := +T_Comp;
            else
               Checks := New_Void;
            end if;
         end;

      elsif Is_Record_Type (Ty_Ext) or else Is_Private_Type (Ty_Ext) then

         --  Generates:
         --  let tmp1 = Discr1.default in <if Ty_Ext is unconstrained>
         --  let tmp1 = Discr1 in         <if Ty_Ext is constrained>
         --  let tmp_exp = any <type> ensures { result.discr1 = tmp1 .. } in
         --  (check_for_f1 expr ->
         --          Field1.default                  <if Field1 has a default>
         --          default_check (Etype (Field1))) <otherwise>
         --  /\ ..

         Ada_Ent_To_Why.Push_Scope (Symbol_Table);

         declare
            Tmp_Exp : constant W_Identifier_Id :=
              New_Temp_Identifier (Ty_Ext, EW_Abstract (Ty_Ext));
            --  Temporary variable for tmp_exp

            Post    : W_Pred_Id := True_Pred;
            --  Post used for the assignment of tmp_exp

            Discrs  : constant Natural :=
              (if Has_Discriminants (Ty_Ext) then
                 Natural (Number_Discriminants (Ty_Ext))
               else 0);
            Tmps    : W_Identifier_Array (1 .. Discrs);
            Binds   : W_Expr_Array (1 .. Discrs);
            --  Arrays to store the bindings for discriminants

            Field   : Node_Id := (if Has_Discriminants (Ty_Ext)
                                  or else Has_Unknown_Discriminants (Ty_Ext)
                                  then First_Discriminant (Ty_Ext)
                                  else Empty);
            Elmt    : Elmt_Id :=
              (if Has_Discriminants (Ty_Ext)
               and then Is_Constrained (Ty_Ext) then
                    First_Elmt (Stored_Constraint (Ty_Ext))
               else No_Elmt);
            T_Comp  : W_Expr_Id;
            I       : Positive := 1;
         begin

            --  Go through discriminants to create the bindings for
            --  let tmp1 = Discr1.default in <if Ty_Ext is unconstrained>
            --  let tmp1 = Discr1 in         <if Ty_Ext is constrained>
            --  Also fills Post with { result.discr1 = tmp1 /\ .. }

            while Present (Field) loop
               if not Is_Completely_Hidden (Field) then

                  Tmps (I) := New_Temp_Identifier
                    (Field, Type_Of_Node (Etype (Field)));

                  --  As discriminants may occur in bounds of types of other
                  --  fields and bounds of default values, store them in the
                  --  Symbol_Table.

                  declare
                     Base_Field : constant Entity_Id :=
                       (if Is_Base_Type (Ty_Ext) then Field
                        else Original_Record_Component (Field));
                     --  Defaults are declared in base types, so they relate
                     --  to discriminants declared in base types.
                  begin

                     --  We need entities of discrimiants for bounds of
                     --  component types...

                     Insert_Entity (Field, Tmps (I));

                     --  and entities of discrimiants of the base type for
                     --  bounds of defaults...

                     if not Is_Base_Type (Ty_Ext) then
                        Insert_Entity (Base_Field, Tmps (I));
                     end if;
                  end;

                  if Is_Constrained (Ty_Ext) then

                     --  Store constrained value of discriminants.

                     Binds (I) :=
                       Transform_Expr
                         (Domain        => EW_Prog,
                          Params        => Params,
                          Expr          => Node (Elmt),
                          Expected_Type => Type_Of_Node (Etype (Field)));
                     Next_Elmt (Elmt);
                  else
                     pragma Assert (Has_Defaulted_Discriminants (Ty_Ext));

                     --  Store default value of discriminants for unconstrained
                     --  record types with default discriminants.

                     Binds (I) :=
                       Transform_Expr
                         (Expr          =>
                            Discriminant_Default_Value (Field),
                          Expected_Type => Type_Of_Node (Etype (Field)),
                          Domain        => EW_Prog,
                          Params        => Params);
                  end if;

                  --  Add new Equality tmp = result.discr to Post

                  Post := +New_And_Then_Expr
                    (Left   => +Post,
                     Right  => New_Comparison
                       (Symbol => Why_Eq,
                        Left   => +Tmps (I),
                        Right  => Insert_Simple_Conversion
                          (Domain => EW_Term,
                           Expr   => New_Ada_Record_Access
                             (Ada_Node => Empty,
                              Domain   => EW_Term,
                              Name     =>
                                +New_Result_Ident (EW_Abstract (Ty_Ext)),
                              Field    => Field,
                              Ty       => Ty_Ext),
                           To     => Type_Of_Node (Etype (Field))),
                        Domain => EW_Pred),
                     Domain => EW_Pred);
               end if;
               Next_Discriminant (Field);
               I := I + 1;
            end loop;

            --  Go through other fields to create the expression
            --  (check_for_f1 expr ->
            --        Field1.default                  <if Field1 has a default>
            --        default_check (Etype (Field1))) <otherwise>
            --  /\ ..

            if Is_Record_Type (Ty_Ext) or else Is_Private_Type (Ty_Ext) then
               Field := First_Component (Ty_Ext);

               while Present (Field) loop
                  if Component_Is_Visible_In_SPARK (Field) then

                     if Present (Expression (Parent (Field))) then

                        --  if Field has a default expression, use it.

                        T_Comp := Transform_Expr
                          (Expr          => Expression (Parent (Field)),
                           Expected_Type => Type_Of_Node (Etype (Field)),
                           Domain        => EW_Prog,
                           Params        => Params);
                     else

                        --  otherwise, use its Field's Etype default value.

                        T_Comp :=
                          +Compute_Default_Check (Etype (Field), Params);
                     end if;

                     if T_Comp /= New_Void then

                        --  Check values of record fields only if they are in
                        --  the proper variant part.

                        T_Comp  := New_Conditional
                          (Domain      => EW_Prog,
                           Condition   => New_Ada_Record_Check_For_Field
                             (Empty, EW_Prog, +Tmp_Exp, Field, Ty_Ext),
                           Then_Part   =>
                             +New_Ignore
                             (Ada_Node => Etype (Field),
                              Prog     => +T_Comp));

                        Checks := Sequence
                          (Left  => Checks,
                           Right => +T_Comp);
                     end if;
                  end if;

                  Next_Component (Field);
               end loop;
            end if;

            --  create bindings for Tmp_Exp
            --  let expr = any <type> ensures { expr.discr1 = tmp1 .. } in

            if Checks /= New_Void and then Is_Record_Type (Ty_Ext) then

                  Checks := +New_Typed_Binding
                    (Domain   => EW_Prog,
                     Name     => Tmp_Exp,
                     Def      =>
                       New_Any_Expr (Ada_Node    => Ty_Ext,
                                     Pre         => True_Pred,
                                     Post        => Post,
                                     Return_Type => EW_Abstract (Ty_Ext)),
                     Context  => +Checks);

            end if;

            --  Generate the bindings if we have some fields to check
            --  or if we need to check the bindings themselves.

            if Checks /= New_Void or else not Is_Constrained (Ty_Ext) then
               for I in 1 .. Discrs loop
                  Checks := +New_Typed_Binding
                    (Domain   => EW_Prog,
                     Name     => Tmps (I),
                     Def      => Binds (I),
                     Context  => +Checks);
               end loop;
            end if;
         end;
         Ada_Ent_To_Why.Pop_Scope (Symbol_Table);
      end if;

      --  If Ty's fullview is in SPARK,
      --  check for absence of runtime errors in Ty's default initial condition
      --  and check that it is implied by the default initialization of Ty.
      --  Generate let x = any Ty in
      --        ignore__ (Def_Init_Cond (x));
      --        assert {Default_Init (x) -> Def_Init_Cond (x)}

      if (Has_Default_Init_Cond (Ty)
            or else
          Has_Inherited_Default_Init_Cond (Ty))
        and then not Is_Private_Type (Ty_Ext)
      then
         declare
            Default_Init_Subp : constant Entity_Id :=
              Default_Init_Cond_Procedure (Ty);
            Default_Init_Expr : constant Node_Id :=
              Get_Expr_From_Check_Only_Proc (Default_Init_Subp);
            Binders           : constant Item_Array :=
              Compute_Subprogram_Parameters (Default_Init_Subp, EW_Prog);
            --  Binder for the reference to the type in the default property.
         begin
            pragma Assert (Binders'Length = 1);

            if Present (Default_Init_Expr) then

               --  Add the binder for the reference to the type to the
               --  Symbol_Table.

               Ada_Ent_To_Why.Push_Scope (Symbol_Table);

               declare
                  Binder : constant Item_Type :=
                    Binders (Binders'First);
                  A      : constant Node_Id :=
                    (case Binder.Kind is
                        when Regular => Binder.Main.Ada_Node,
                        when others  => raise Program_Error);
               begin
                  pragma Assert (Present (A));

                  if Present (A) then
                     Ada_Ent_To_Why.Insert (Symbol_Table,
                                            Unique_Entity (A),
                                            Binder);
                  end if;

                  declare
                     W_Def_Init_Prog : constant W_Expr_Id :=
                       Transform_Expr
                         (Expr          => Default_Init_Expr,
                          Domain        => EW_Prog,
                          Params        => Params);
                     W_Def_Init_Expr : constant W_Expr_Id :=
                       Transform_Expr
                         (Expr          => Default_Init_Expr,
                          Domain        => EW_Pred,
                          Params        => Params);
                     Condition       : constant W_Pred_Id :=
                       Compute_Default_Init
                         (Expr           => Insert_Simple_Conversion
                            (Domain   => EW_Term,
                             Expr     => +Binder.Main.B_Name,
                             To       => Type_Of_Node (Ty_Ext)),
                          Ty             => Ty_Ext,
                          Skip_Last_Cond => True_Term);
                     Def_Init_Check  : constant W_Expr_Id :=
                       New_Conditional
                         (Domain      => EW_Pred,
                          Condition   => +Condition,
                          Then_Part   => W_Def_Init_Expr);
                  begin

                     Checks := Sequence
                       (New_Ignore (Prog => Checks),
                        +New_Typed_Binding
                          (Domain   => EW_Prog,
                           Name     => Binder.Main.B_Name,
                           Def      =>
                             New_Any_Expr
                               (Pre         => True_Pred,
                                Post        => True_Pred,
                                Return_Type => Get_Typ (Binder.Main.B_Name)),
                           Context  =>
                             +Sequence (New_Ignore (Prog => +W_Def_Init_Prog),
                             New_Assert
                               (Pred        => +New_VC_Expr
                                  (Ada_Node => Ty,
                                   Expr     => Def_Init_Check,
                                   Reason   => VC_Default_Initial_Condition,
                                   Domain   => EW_Pred),
                                Assert_Kind => EW_Check))));
                  end;
               end;

               Ada_Ent_To_Why.Pop_Scope (Symbol_Table);
            end if;
         end;
      end if;

      return Checks;
   end Compute_Default_Check;

   --------------------------
   -- Compute_Default_Init --
   --------------------------

   function Compute_Default_Init
     (Expr           : W_Expr_Id;
      Ty             : Entity_Id;
      Params         : Transformation_Params := Body_Params;
      Skip_Last_Cond : W_Term_Id := False_Term;
      Use_Pred       : Boolean := True) return W_Pred_Id is

      Ty_Ext     : constant Entity_Id := Retysp (Ty);
      Tmp        : constant W_Expr_Id := New_Temp_For_Expr (Expr);
      Assumption : W_Expr_Id := +True_Pred;
      Variables  : Flow_Id_Sets.Set;
   begin

      --  If Use_Precomputed_Func is true, then we already have generated a
      --  predicate for the default initial value of elements of type Ty_Ext,
      --  except if the type is an itype or if it is standard boolen.

      if Use_Pred
        and then not Is_Itype (Ty_Ext)
        and then not Is_Standard_Boolean_Type (Ty_Ext)
      then
         Variables_In_Default_Init (Ty_Ext, Variables);

         declare
            Vars  : constant W_Expr_Array :=
              Get_Args_From_Variables
                (To_Name_Set (Variables), Params.Ref_Allowed);
            Num_B : constant Positive := 2 + Vars'Length;
            Args  : W_Expr_Array (1 .. Num_B);
         begin

            Args (1) := Insert_Simple_Conversion
              (Domain         => EW_Term,
               Expr           => Expr,
               To             => Type_Of_Node (Ty_Ext),
               Force_No_Slide => True);
            Args (2) := +Skip_Last_Cond;
            Args (3 .. Num_B) := Vars;

            return New_Call (Name => E_Symb (Ty_Ext, WNE_Default_Init),
                             Args => Args,
                             Typ  => EW_Bool_Type);
         end;
      end if;

      if Is_Scalar_Type (Ty_Ext) then
         if Has_Default_Aspect (Ty_Ext) then
            declare
               Default_Expr : constant W_Expr_Id :=
                 Transform_Expr
                      (Expr          => Default_Aspect_Value (Ty_Ext),
                       Expected_Type => Base_Why_Type (Ty_Ext),
                       Domain        => EW_Term,
                       Params        => Params);
            begin
               Assumption := New_Comparison
                 (Symbol => Why_Eq,
                  Left   => Insert_Simple_Conversion
                    (Ada_Node => Empty,
                     Domain   => EW_Pred,
                     Expr     => Tmp,
                     To       => Base_Why_Type (Ty_Ext)),
                  Right  => Default_Expr,
                  Domain => EW_Pred);
            end;
         end if;
      elsif Is_Array_Type (Ty_Ext)
        and then Ekind (Ty_Ext) /= E_String_Literal_Subtype
      then
         pragma Assert (Is_Constrained (Ty_Ext));

         --  Generates:
         --  forall i1 : int ..
         --   in_range (i1) /\ .. ->
         --    get (<Expr>, i1, ...) = <Default_Component_Value>    <if any>
         --    default_init (get (<Expr>, i1, ...), Component_Type) <otherwise>

         declare
            Num_Dim    : constant Positive :=
              Positive (Number_Dimensions (Ty_Ext));
            Vars       : Binder_Array (1 .. Num_Dim);
            Indices    : W_Expr_Array (1 .. Num_Dim);
            Range_Expr : W_Pred_Id := True_Pred;
            Index      : Node_Id := First_Index (Ty_Ext);
            I          : Positive := 1;
            T_Acc      : W_Expr_Id;
         begin

            --  Generate variables i1 ..
            --  and the condition in_range (i1) /\ ..

            while Present (Index) loop
               declare
                  Typ : constant W_Type_Id := Base_Why_Type_No_Bool
                    (Index);
                  Tmp : constant W_Identifier_Id := New_Temp_Identifier
                    (Typ => Typ);
               begin
                  Vars (I) := Binder_Type'(Ada_Node => Empty,
                                           B_Name   => Tmp,
                                           B_Ent    => Null_Entity_Name,
                                           Mutable  => False);
                  Indices (I) := +Tmp;
               end;

               Range_Expr := +New_And_Then_Expr
                 (Left   => +Range_Expr,
                  Right  =>
                    New_Range_Expr
                      (Domain => EW_Pred,
                       Low    => Insert_Conversion_To_Rep_No_Bool
                         (EW_Term,
                          Get_Array_Attr (Domain => EW_Term,
                                          Ty     => Ty_Ext,
                                          Attr   => Attribute_First,
                                          Dim    => I)),
                       High   => Insert_Conversion_To_Rep_No_Bool
                         (EW_Term,
                          Get_Array_Attr (Domain => EW_Term,
                                          Ty     => Ty_Ext,
                                          Attr   => Attribute_Last,
                                          Dim    => I)),
                       Expr   => Indices (I)),
                  Domain => EW_Pred);
               Next_Index (Index);
               I := I + 1;
            end loop;

            T_Acc := New_Array_Access (Empty, Tmp, Indices, EW_Term);

            if Has_Default_Aspect (Ty_Ext) then

               --  if Ty_Ext as a Default_Component_Value aspect,
               --  generate get (<Expr>, i1, ...) = <Default_Component_Value>

               Assumption := New_Comparison
                 (Symbol => Why_Eq,
                  Left   => Insert_Simple_Conversion
                    (Domain => EW_Term,
                     Expr   => T_Acc,
                     To     => Type_Of_Node (Component_Type (Ty_Ext))),
                  Right  => Transform_Expr
                    (Expr          => Default_Aspect_Component_Value (Ty_Ext),
                     Expected_Type => Type_Of_Node (Component_Type (Ty_Ext)),
                     Domain        => EW_Term,
                     Params        => Params),
                  Domain => EW_Pred);
            else

               --  otherwise, use its Component_Type default value.

               Assumption := +Compute_Default_Init
                 (Expr     => T_Acc,
                  Ty       => Component_Type (Ty_Ext),
                  Params   => Params,
                  Use_Pred => Use_Pred);
            end if;

            if Assumption /= +True_Pred then
               Assumption := New_Conditional
                 (Domain      => EW_Pred,
                  Condition   => +Range_Expr,
                  Then_Part   => Assumption,
                  Typ         => EW_Bool_Type);

               Assumption := +New_Universal_Quantif
                 (Binders  => Vars,
                  Pred     => +Assumption);
            end if;
         end;

      elsif Is_Record_Type (Ty_Ext) or else Is_Private_Type (Ty_Ext) then

         --  Generates:
         --  let tmp1 = <Expr>.rec__disc1 in
         --  <Expr>.is_constrained = False /\ <if Ty_Ext as default discrs>
         --  <Expr>.rec__disc1 = Discr1.default  <if Ty_Ext is unconstrained>
         --  <Expr>.rec__disc1 = Discr1 /\ ..    <if Ty_Ext is constrained>
         --  (check_for_field1 expr ->
         --      <Expr>.rec__field1 = Field1.def      <if Field1 has a default>
         --      default_init (<Expr>.rec__field1, Etype (Field1))) <otherwise>
         --  /\ ..

         Ada_Ent_To_Why.Push_Scope (Symbol_Table);

         declare
            R_Expr : constant W_Expr_Id :=
              Insert_Simple_Conversion (Ada_Node => Ty,
                                        Domain   => EW_Term,
                                        Expr     => Tmp,
                                        To       => EW_Abstract (Ty_Ext));
            --  Expression that should be used for the access

            Discrs : constant Natural :=
              (if Has_Discriminants (Ty_Ext)
               then Natural (Number_Discriminants (Ty_Ext))
               else 0);
            Tmps   : W_Identifier_Array (1 .. Discrs);
            Binds  : W_Expr_Array (1 .. Discrs);
            --  Arrays to store the bindings for discriminants

            Field  : Node_Id := (if Has_Discriminants (Ty_Ext)
                                 or else Has_Unknown_Discriminants (Ty_Ext)
                                 then First_Discriminant (Ty_Ext)
                                 else Empty);
            Elmt   : Elmt_Id :=
              (if Has_Discriminants (Ty_Ext)
               and then Is_Constrained (Ty_Ext)
               then First_Elmt (Stored_Constraint (Ty_Ext))
               else No_Elmt);
            T_Comp : W_Expr_Id;
            I      : Positive := 1;
         begin
            --  if Ty_Ext as default discrs, generate
            --     <Expr>.is_constrained = False

            if Has_Defaulted_Discriminants (Ty_Ext) and then
              not Is_Constrained (Ty_Ext)
            then
               --  The variable is not constrained.

               Assumption :=
                 New_Call
                   (Domain => EW_Pred,
                    Typ    => EW_Bool_Type,
                    Name   => Why_Eq,
                    Args =>
                      (1 =>
                             New_Is_Constrained_Access
                         (Ada_Node => Ty,
                          Domain   => EW_Term,
                          Name     => Tmp,
                          Ty       => Ty_Ext),
                       2 => +False_Term));
            end if;

            --  if Ty_Ext is tagged, generate
            --     <Expr>.attr__tag = <Ty_Ext>.__tag

            if Is_Tagged_Type (Ty_Ext) then
               Assumption :=
                 New_Call
                   (Domain => EW_Pred,
                    Typ    => EW_Bool_Type,
                    Name   => Why_Eq,
                    Args =>
                      (1 => New_Tag_Access
                         (Ada_Node => Ty,
                          Domain   => EW_Term,
                          Name     => Tmp,
                          Ty       => Ty_Ext),
                       2 => +E_Symb (Ty_Ext, WNE_Tag)));
            end if;

            --  Go through discriminants to create
            --  <Expr>.rec__disc1 = Discr1.default <if Ty_Ext is unconstrained>
            --  <Expr>.rec__disc1 = Discr1 /\ ..   <if Ty_Ext is constrained>

            while Present (Field) loop
               if not Is_Completely_Hidden (Field) then

                  Tmps (I) := New_Temp_Identifier
                    (Field, Type_Of_Node (Etype (Field)));

                  Binds (I) := Insert_Simple_Conversion
                    (Domain => EW_Term,
                     Expr   => New_Ada_Record_Access
                       (Empty, EW_Term, R_Expr, Field, Ty_Ext),
                     To     => Type_Of_Node (Etype (Field)));

                  --  As discriminants may occur in bounds of types of other
                  --  fields and bounds of default values, store them in the
                  --  Symbol_Table.

                  declare
                     Base_Field : constant Entity_Id :=
                       (if Is_Base_Type (Ty_Ext) then Field
                        else Original_Record_Component (Field));
                     --  Defaults are declared in base types, so they relate
                     --  to discriminants declared in base types.
                  begin

                     --  We need entities of discrimiants for bounds of
                     --  component types...

                     Insert_Entity (Field, Tmps (I));

                     --  and entities of discrimiants of the base type for
                     --  bounds of defaults

                     if not Is_Base_Type (Ty_Ext) then
                        Insert_Entity (Base_Field, Tmps (I));
                     end if;
                  end;

                  if Is_Constrained (Ty_Ext) then

                     --  Generate <Expr>.rec__disc1 = Discr1

                     Assumption :=
                       New_And_Then_Expr
                         (Left   => Assumption,
                          Right  => New_Comparison
                            (Symbol    => Why_Eq,
                             Left   => Binds (I),
                             Right  => Transform_Expr
                               (Domain        => EW_Term,
                                Params        => Params,
                                Expr          => Node (Elmt),
                                Expected_Type =>
                                  Type_Of_Node (Etype (Field))),
                             Domain => EW_Pred),
                          Domain => EW_Pred);
                     Next_Elmt (Elmt);
                  else
                     pragma Assert (Has_Defaulted_Discriminants (Ty_Ext));

                     --  Generate <Expr>.rec__disc1 = Discr1.default

                     Assumption :=
                       New_And_Then_Expr
                         (Left   => Assumption,
                          Right  => New_Comparison
                            (Symbol => Why_Eq,
                             Left   => Binds (I),
                             Right  => Transform_Expr
                               (Expr          =>
                                    Discriminant_Default_Value (Field),
                                Expected_Type =>
                                  Type_Of_Node (Etype (Field)),
                                Domain        => EW_Term,
                                Params        => Params),
                             Domain => EW_Pred),
                          Domain => EW_Pred);
                  end if;
               end if;
               Next_Discriminant (Field);
               I := I + 1;
            end loop;

            --  Go through other fields to create the expression
            --  (check_for_field1 expr ->
            --   <Expr>.rec__field1 = Field1.def      <if Field1 has a default>
            --   default_init (<Expr>.rec__field1, Etype (Field1))) <otherwise>
            --  /\ ..

            if Is_Record_Type (Ty_Ext) or else Is_Private_Type (Ty_Ext) then
               Field := First_Component (Ty_Ext);

               while Present (Field) loop
                  if Component_Is_Visible_In_SPARK (Field) then
                     if Present (Expression (Parent (Field))) then

                        --  if Field has a default expression, use it.
                        --   <Expr>.rec__field1 = Field1.default

                        T_Comp := New_Comparison
                          (Symbol => Why_Eq,
                           Left   => Insert_Simple_Conversion
                             (Domain => EW_Term,
                              Expr   => New_Ada_Record_Access
                                (Empty, EW_Term, Tmp, Field, Ty_Ext),
                              To     => Type_Of_Node (Etype (Field))),
                           Right  => Transform_Expr
                             (Expr          => Expression (Parent (Field)),
                              Expected_Type => Type_Of_Node (Etype (Field)),
                              Domain        => EW_Term,
                              Params        => Params),
                           Domain => EW_Pred);
                     else

                        --  otherwise, use its Field's Etype default value.
                        --   default_init (<Expr>.rec__field1, Etype (Field1)))

                        T_Comp := +Compute_Default_Init
                          (New_Ada_Record_Access
                             (Empty, EW_Term, Tmp, Field, Ty_Ext),
                           Etype (Field),
                           Params => Params,
                           Use_Pred => Use_Pred);
                     end if;

                     if T_Comp /= +True_Pred then

                        --  Assume values of record fields only if they are in
                        --  the proper variant part.

                        T_Comp  := New_Conditional
                          (Domain      => EW_Pred,
                           Condition   => New_Ada_Record_Check_For_Field
                             (Empty, EW_Term, Tmp, Field, Ty_Ext),
                           Then_Part   => T_Comp);

                        Assumption := New_And_Then_Expr
                          (Left   => Assumption,
                           Right  => T_Comp,
                           Domain => EW_Pred);
                     end if;
                  end if;

                  Next_Component (Field);
               end loop;
            end if;

            --  Generate the bindings for discriminants.

            if Assumption /= +True_Pred then
               for I in 1 .. Discrs loop
                  Assumption := New_Typed_Binding
                    (Domain   => EW_Pred,
                     Name     => Tmps (I),
                     Def      => Binds (I),
                     Context  => Assumption);
               end loop;
            end if;
         end;
         Ada_Ent_To_Why.Pop_Scope (Symbol_Table);
      end if;

      --  If Skip_Last_Cond is False, assume the default initial condition for
      --  Ty.

      if Has_Default_Init_Cond (Ty)
        or else Has_Inherited_Default_Init_Cond (Ty)
      then
         declare
            Init_Subp : constant Entity_Id :=
              Default_Init_Cond_Procedure (Ty);
            Init_Expr : constant Node_Id :=
              Get_Expr_From_Check_Only_Proc (Init_Subp);
            Init_Param : constant Entity_Id :=
              Defining_Entity (First (Parameter_Specifications
                (Subprogram_Specification (Init_Subp))));
            Init_Id    : constant W_Identifier_Id :=
              New_Temp_Identifier (Init_Param, Get_Type (Tmp));
            T          : W_Pred_Id;

         begin
            if Present (Init_Expr) then
               Ada_Ent_To_Why.Push_Scope (Symbol_Table);

               --  Register the temporary identifier Init_Id for parameter
               --  Init_Param in the symbol table. This ensures both that a
               --  distinct name is used each time (preventing name capture),
               --  and that the type of Tmp is used as the type used to
               --  represent Init_Param (avoiding type conversion).

               Insert_Entity (Init_Param, Init_Id);

               --  Transform the default init expression into Why3

               T := +Transform_Expr (Expr   => Init_Expr,
                                     Domain => EW_Pred,
                                     Params => Params);

               --  Relate the name Init_Id used in the default init expression
               --  to the value Tmp for which the predicate is checked.

               T := New_Binding (Name    => Init_Id,
                                 Def     => Tmp,
                                 Context => +T,
                                 Typ     => Get_Type (+T));

               --  Only take default init condition into account if
               --  Skip_Last_Cond is False.

               T := New_Conditional (Condition => +Skip_Last_Cond,
                                     Then_Part => +True_Pred,
                                     Else_Part => +T,
                                     Typ       => EW_Bool_Type);

               Assumption := New_And_Then_Expr (Left   => Assumption,
                                                Right  => +T,
                                                Domain => EW_Pred);

               Ada_Ent_To_Why.Pop_Scope (Symbol_Table);
            end if;
         end;
      end if;

      if Assumption = +True_Pred then
         return True_Pred;
      else
         return +Binding_For_Temp
           (Domain => EW_Pred, Tmp => Tmp, Context => Assumption);
      end if;
   end Compute_Default_Init;

   -------------------------------
   -- Compute_Dynamic_Invariant --
   -------------------------------

   function Compute_Dynamic_Invariant
     (Expr          : W_Term_Id;
      Ty            : Entity_Id;
      Initialized   : W_Term_Id := True_Term;
      Only_Var      : W_Term_Id := True_Term;
      Top_Predicate : W_Term_Id := True_Term;
      Params        : Transformation_Params := Body_Params;
      Use_Pred      : Boolean := True) return W_Pred_Id
   is
      T : W_Pred_Id;

      --  If Ty's fullview is in SPARK, go to its underlying type to check its
      --  kind.

      Ty_Spec   : constant Entity_Id :=
        (if Is_Class_Wide_Type (Ty) then Get_Specific_Type_From_Classwide (Ty)
         else Ty);
      Ty_Ext    : constant Entity_Id := Retysp (Ty_Spec);
      Variables : Flow_Id_Sets.Set;

   begin
      --  If Use_Pred is true, then we already have generated a predicate
      --  for the dynamic invariant of elements of type Ty_Ext, except if the
      --  type is an itype or if it is standard boolean. We also avoid using
      --  the predicate for objects in split form as it would introduce an
      --  unnecessary conversion harmful to provers.

      if Use_Pred
        and then not Is_Itype (Ty_Ext)
        and then not Is_Standard_Boolean_Type (Ty_Ext)
        and then Eq_Base (Type_Of_Node (Ty_Ext), Get_Type (+Expr))
      then
         Variables_In_Dynamic_Invariant (Ty_Ext, Variables);

         declare
            Vars  : constant W_Expr_Array :=
              Get_Args_From_Variables
                (To_Name_Set (Variables), Params.Ref_Allowed);
            Num_B : constant Positive := 4 + Vars'Length;
            Args  : W_Expr_Array (1 .. Num_B);

         begin
            Args (1) := +Expr;
            Args (2) := +Initialized;
            Args (3) := +Only_Var;
            Args (4) := +Top_Predicate;
            Args (5 .. Num_B) := Vars;

            return New_Call (Name => E_Symb (E => Ty_Ext,
                                             S => WNE_Dynamic_Invariant),
                             Args => Args,
                             Typ  => EW_Bool_Type);
         end;
      end if;

      --  Dynamic property of the type itself

      if Type_Is_Modeled_As_Base (Ty_Ext)
        or else (Is_Scalar_Type (Ty_Ext)
                 and then Get_Type_Kind (Get_Type (+Expr)) = EW_Split)
      then
         T := +New_Dynamic_Property (Domain => EW_Pred,
                                     Ty     => Ty_Ext,
                                     Expr   => +Expr,
                                     Params => Params);

         --  If a scalar variable is not initialized, then its dynamic property
         --  may be false. As initialization is checked separately by flow
         --  analysis, we can assume that the variable is in bound as long as
         --  it does not introduce any unsoundness (the range is not empty).

         if T /= True_Pred then
            declare
               Why_Rep_Type : constant W_Type_Id := Base_Why_Type (Ty_Ext);
               Le_Op        : constant W_Identifier_Id :=
                 (if Why_Rep_Type = EW_Real_Type then Real_Infix_Le
                  elsif Why_Type_Is_BitVector (Why_Rep_Type) then
                    MF_BVs (Why_Rep_Type).Ule
                  else Int_Infix_Le);
               First        : constant W_Expr_Id :=
                 Insert_Simple_Conversion
                   (Domain   => EW_Term,
                    Expr     => New_Attribute_Expr
                      (Ty       => Ty_Ext,
                       Domain   => EW_Term,
                       Attr     => Attribute_First,
                       Params   => Params),
                    To       => Why_Rep_Type);
               Last        : constant W_Expr_Id :=
                 Insert_Simple_Conversion
                   (Domain   => EW_Term,
                    Expr     => New_Attribute_Expr
                      (Ty     => Ty_Ext,
                       Domain => EW_Term,
                       Attr   => Attribute_Last,
                       Params => Params),
                    To       => Why_Rep_Type);
               Fst_Le_Last : constant W_Pred_Id :=
                 New_Call (Name     => Le_Op,
                           Typ     => EW_Bool_Type,
                           Args    => (First, Last));
            begin
               T := +W_Expr_Id'
                 (New_Conditional
                    (Domain      => EW_Pred,
                     Condition   =>
                       New_Or_Else_Expr (+Initialized, +Fst_Le_Last, EW_Pred),
                     Then_Part   => +T,
                     Typ         => EW_Bool_Type));
            end;
         end if;
      elsif Is_Array_Type (Ty_Ext)
        and then not Is_Static_Array_Type (Ty_Ext)
      then
         T := +New_Dynamic_Property (Domain => EW_Pred,
                                     Ty     => Ty_Ext,
                                     Expr   => +Expr,
                                     Params => Params);

         --  For arrays, also assume the value of its bounds

         if Is_Constrained (Ty_Ext) then
            declare
               Index : Node_Id := First_Index (Ty_Ext);
               I     : Positive := 1;
            begin
               while Present (Index) loop
                  declare
                     Rng       : constant Node_Id := Get_Range (Index);
                     Rng_Ty    : constant W_Type_Id :=
                           Base_Why_Type_No_Bool (Etype (Index));
                     Low_Expr  : constant W_Expr_Id :=
                       Transform_Expr (Low_Bound (Rng), Rng_Ty,
                                       EW_Term, Params);
                     First_Eq  : constant W_Pred_Id :=
                       New_Call
                         (Name => Why_Eq,
                          Typ  => EW_Bool_Type,
                          Args =>
                            (1 => Insert_Conversion_To_Rep_No_Bool
                               (EW_Term,
                                +Get_Array_Attr
                                  (Domain => EW_Term,
                                   Expr   => +Expr,
                                   Attr   => Attribute_First,
                                   Dim    => I)),
                             2 => Low_Expr));
                     High_Expr : constant W_Expr_Id :=
                       Transform_Expr (High_Bound (Rng), Rng_Ty,
                                       EW_Term, Params);
                     Last_Eq   : constant W_Pred_Id :=
                       New_Call
                         (Name => Why_Eq,
                          Typ  => EW_Bool_Type,
                          Args =>
                            (1 => Insert_Conversion_To_Rep_No_Bool
                               (EW_Term,
                                +Get_Array_Attr
                                  (Domain => EW_Term,
                                   Expr   => +Expr,
                                   Attr   => Attribute_Last,
                                   Dim    => I)),
                             2 => High_Expr));
                  begin

                     --  Assuming the value of Ty's bounds

                     T := +New_And_Then_Expr
                       (Left   => +T,
                        Right  =>
                          +New_And_Then_Expr (Left   => +First_Eq,
                                              Right  => +Last_Eq,
                                              Domain => EW_Pred),
                        Domain => EW_Pred);

                  end;
                  Next_Index (Index);
                  I := I + 1;
               end loop;
            end;
         end if;

         T := New_Conditional
           (Condition   => +Only_Var,
            Then_Part   => +True_Pred,
            Else_Part   => +T,
            Typ         => EW_Bool_Type);

      elsif Has_Discriminants (Ty_Ext)
        and then Is_Constrained (Ty_Ext)
      then
         T := New_Conditional
           (Condition   => +Only_Var,
            Then_Part   => +True_Pred,
            Else_Part   => +New_Dynamic_Property (Domain => EW_Pred,
                                                  Ty     => Ty_Ext,
                                                  Expr   => +Expr,
                                                  Params => Params),
            Typ         => EW_Bool_Type);
      else
         T := True_Pred;
      end if;

      --  Add possible dynamic predicate. This is only valid for initialized
      --  data, when the top predicate should be included.

      declare
         Typ_Pred : constant W_Pred_Id :=
           Compute_Dynamic_Predicate
             (Expr, Ty_Ext, Params, Use_Pred => False);
         Check_Pred : constant W_Pred_Id :=
           New_Conditional
             (Condition => +Top_Predicate,
              Then_Part => New_Conditional (Domain    => EW_Pred,
                                            Condition => +Initialized,
                                            Then_Part => +Typ_Pred,
                                            Typ       => EW_Bool_Type),
              Typ       => EW_Bool_Type);

      begin
         if Typ_Pred /= True_Pred then
            T := +New_And_Then_Expr (Left   => +T,
                                     Right  => +Check_Pred,
                                     Domain => EW_Pred);
         end if;
      end;

      --  Compute dynamic invariant for its components

      if Is_Array_Type (Ty_Ext)
        and then Ekind (Ty_Ext) /= E_String_Literal_Subtype
      then

         --  Generates:
         --  forall i1 .. in : int. in_range i1 /\ .. /\ in_range in ->
         --    Dynamic_Invariant (get <Expr> i1 .. in)

         declare
            Dim        : constant Positive :=
              Positive (Number_Dimensions (Ty_Ext));
            Vars       : Binder_Array (1 .. Dim);
            Indices    : W_Expr_Array (1 .. Dim);
            Range_Expr : W_Pred_Id := True_Pred;
            Index      : Node_Id := First_Index (Ty_Ext);
            I          : Positive := 1;
            T_Comp     : W_Expr_Id;
            Tmp        : W_Identifier_Id;
            Q_Expr     : W_Pred_Id;
         begin
            while Present (Index) loop
               Tmp := New_Temp_Identifier
                 (Typ => Base_Why_Type_No_Bool (Index));
               Vars (I) := Binder_Type'(Ada_Node => Empty,
                                        B_Name   => Tmp,
                                        B_Ent    => Null_Entity_Name,
                                        Mutable  => False);
               Indices (I) := +Tmp;
               Range_Expr := +New_And_Expr
                 (Left   => +Range_Expr,
                  Right  =>
                    New_Range_Expr
                      (Domain => EW_Pred,
                       Low    => Insert_Conversion_To_Rep_No_Bool
                         (EW_Term,
                          Get_Array_Attr (Domain => EW_Term,
                                          Expr   => +Expr,
                                          Attr   => Attribute_First,
                                          Dim    => I)),
                       High   => Insert_Conversion_To_Rep_No_Bool
                         (EW_Term,
                          Get_Array_Attr (Domain => EW_Term,
                                          Expr   => +Expr,
                                          Attr   => Attribute_Last,
                                          Dim    => I)),
                       Expr   => +Tmp),
                  Domain => EW_Pred);
               Next_Index (Index);
               I := I + 1;
            end loop;

            pragma Assert (I = Indices'Last + 1);

            --  Recursively call Compute_Dynamic_Invariant on the array
            --  components. Additional parameters are unchanged expect for
            --  Only_Var set to false (as a constant subcomponent of a variable
            --  toplevel object needs to be considered as variable too) and
            --  Top_Predicate set to true (as the decision to include or not
            --  the top predicate does not apply to subcomponents).

            T_Comp :=
              +Compute_Dynamic_Invariant
                 (Expr          =>
                    +New_Array_Access (Empty, +Expr, Indices, EW_Term),
                  Ty            => Component_Type (Ty_Ext),
                  Initialized   => Initialized,
                  Only_Var      => False_Term,
                  Top_Predicate => True_Term,
                  Params        => Params,
                  Use_Pred      => Use_Pred);

            --  If elements of an array have default discriminants and are not
            --  constrained then 'Constrained returns false on them.

            if Has_Defaulted_Discriminants (Retysp (Component_Type (Ty_Ext)))
              and then not Is_Constrained (Retysp (Component_Type (Ty_Ext)))
            then
               T_Comp := New_And_Expr
                 (Left   => +T_Comp,
                  Right  =>
                    New_Call
                      (Domain => EW_Term,
                       Typ    => EW_Bool_Type,
                       Name   => Why_Eq,
                       Args   =>
                         (1 =>
                                New_Is_Constrained_Access
                            (Ada_Node => Empty,
                             Domain   => EW_Term,
                             Name     =>
                               New_Array_Access
                                 (Empty, +Expr, Indices, EW_Term),
                             Ty       => Component_Type (Ty_Ext)),
                          2 => +False_Term)),
                  Domain => EW_Pred);
            end if;

            if T_Comp /= +True_Pred then
               T_Comp := New_Conditional
                 (Domain      => EW_Pred,
                  Condition   => +Range_Expr,
                  Then_Part   => T_Comp,
                  Typ         => EW_Bool_Type);

               Q_Expr := New_Universal_Quantif
                 (Binders  => Vars,
                  Pred     => +T_Comp);

               if T = True_Pred then
                  T := Q_Expr;
               else
                  T := +New_And_Then_Expr (Left   => +T,
                                           Right  => +Q_Expr,
                                           Domain => EW_Pred);
               end if;
            end if;
         end;

      elsif (Is_Record_Type (Ty_Ext) and then not Is_String_Type (Ty_Ext))
        or else Is_Private_Type (Ty_Ext)
      then

         --  Generates:
         --  (check_for_f1 <Expr> -> Dynamic_Invariant <Expr>.rec__f1)
         --  /\ .. /\ (check_for_fn <Expr> -> Dynamic_Invariant <Expr>.rec__fn)
         --  As discriminants may occur in bounds of types of other fields,
         --  store them in the Symbol_Table.

         Ada_Ent_To_Why.Push_Scope (Symbol_Table);

         declare
            R_Expr  : constant W_Expr_Id :=
              Insert_Simple_Conversion (Ada_Node => Ty,
                                        Domain   => EW_Term,
                                        Expr     => +Expr,
                                        To       => EW_Abstract (Ty_Ext));
            Discrs  : constant Natural :=
              (if Has_Discriminants (Ty_Ext) then
                 Natural (Number_Discriminants (Ty_Ext))
               else 0);
            Field   : Node_Id := First_Component_Or_Discriminant (Ty_Ext);
            T_Comp  : W_Pred_Id;
            T_Guard : W_Pred_Id;
            F_Expr  : W_Expr_Id;
            R_Acc   : W_Expr_Id;
            Tmps    : W_Identifier_Array (1 .. Discrs);
            Binds   : W_Expr_Array (1 .. Discrs);
            I       : Positive := 1;
         begin
            while Present (Field) loop
               if (Is_Record_Type (Ty_Ext)
                   and then Component_Is_Visible_In_SPARK (Field))
                 or else (Ekind (Field) = E_Discriminant
                          and then Is_Not_Hidden_Discriminant (Field))
               then

                  R_Acc := New_Ada_Record_Access
                    (Empty, EW_Term, R_Expr, Field, Ty_Ext);

                  if Ekind (Field) = E_Discriminant then
                     Tmps (I) := New_Temp_Identifier
                       (Field, EW_Abstract (Etype (Field)));
                     Binds (I) := R_Acc;
                     Insert_Entity (Field, Tmps (I));
                  end if;

                  --  Recursively call Compute_Dynamic_Invariant on the record
                  --  components. Additional parameters are unchanged expect
                  --  for Only_Var set to false (as a constant subcomponent
                  --  of a variable toplevel object needs to be considered
                  --  as variable too) and Top_Predicate set to true (as the
                  --  decision to include or not the top predicate does not
                  --  apply to subcomponents).

                  T_Comp :=
                    Compute_Dynamic_Invariant
                      (Expr          => +R_Acc,
                       Ty            => Etype (Field),
                       Initialized   => Initialized,
                       Only_Var      => False_Term,
                       Top_Predicate => True_Term,
                       Params        => Params,
                       Use_Pred      => Use_Pred);

                  --  If fields of a record have default discriminants and are
                  --  not constrained then 'Constrained returns false on them.

                  if Has_Defaulted_Discriminants (Retysp (Etype (Field)))
                    and then not Is_Constrained (Retysp (Etype (Field)))
                  then
                     T_Comp := +New_And_Expr
                       (Left   => +T_Comp,
                        Right  =>
                          New_Call
                            (Domain   => EW_Term,
                             Name     => Why_Eq,
                             Typ      => EW_Bool_Type,
                             Args =>
                               (1 =>
                                      New_Is_Constrained_Access
                                  (Ada_Node => Empty,
                                   Domain   => EW_Term,
                                   Name     => R_Acc,
                                   Ty       => Etype (Field)),
                                2 => +False_Term)),
                        Domain => EW_Pred);
                  end if;

                  if T_Comp /= True_Pred then
                     T_Guard := (if Ekind (Field) = E_Discriminant
                                 then True_Pred
                                 else +New_Ada_Record_Check_For_Field
                                   (Empty, EW_Pred, R_Expr, Field, Ty_Ext));

                     F_Expr  := New_Conditional (Domain      => EW_Pred,
                                                 Condition   => +T_Guard,
                                                 Then_Part   => +T_Comp);

                     if T = True_Pred then
                        T := +F_Expr;
                     else
                        T := +New_And_Then_Expr (Left   => +T,
                                                 Right  => +F_Expr,
                                                 Domain => EW_Pred);
                     end if;
                  end if;
               end if;

               Next_Component_Or_Discriminant (Field);
               I := I + 1;
            end loop;

            if T /= True_Pred then
               for I in 1 .. Discrs loop
                  T := +New_Typed_Binding
                    (Domain   => EW_Pred,
                     Name     => Tmps (I),
                     Def      => Binds (I),
                     Context  => +T);
               end loop;
            end if;
         end;
         Ada_Ent_To_Why.Pop_Scope (Symbol_Table);
      end if;

      return T;
   end Compute_Dynamic_Invariant;

   -------------------------------
   -- Compute_Dynamic_Predicate --
   -------------------------------

   function Compute_Dynamic_Predicate
     (Expr     : W_Term_Id;
      Ty       : Entity_Id;
      Params   : Transformation_Params := Body_Params;
      Use_Pred : Boolean := True) return W_Pred_Id
   is
      Result : W_Pred_Id;

      --  If Ty's fullview is in SPARK, go to its underlying type to check its
      --  kind.

      Ty_Ext : constant Entity_Id := Retysp (Ty);

   begin
      if not Has_Predicates (Ty_Ext) then
         Result := True_Pred;

      --  If Use_Pred is true, then we already have generated a predicate for
      --  the dynamic predicate of elements of type Ty_Ext. We also avoid using
      --  the predicate for objects in split form as it would introduce an
      --  unnecessary conversion harmful to provers.

      elsif Use_Pred
        and then Eq_Base (Type_Of_Node (Ty_Ext), Get_Type (+Expr))
      then
         Result := New_Predicate_Call (Ty_Ext, Expr, Params);

      else
         declare
            Pred_Subp  : constant Entity_Id := Predicate_Function (Ty);
            Pred_Expr  : constant Node_Id :=
              Get_Expr_From_Return_Only_Func (Pred_Subp);
            Pred_Param : constant Entity_Id :=
              Defining_Entity (First (Parameter_Specifications
                               (Subprogram_Specification (Pred_Subp))));
            Pred_Id    : constant W_Identifier_Id :=
              New_Temp_Identifier (Pred_Param, Get_Type (+Expr));

         begin
            Ada_Ent_To_Why.Push_Scope (Symbol_Table);

            --  Register the temporary identifier Pred_Id for parameter
            --  Pred_Param in the symbol table. This ensures both that a
            --  distinct name is used each time (preventing name capture), and
            --  that the type of Expr is used as the type used to represent
            --  Pred_Param (avoiding type conversion).

            if Get_Type_Kind (Get_Type (+Expr)) = EW_Split
              and then Has_Array_Type (Ty_Ext)
            then
               declare
                  E : constant Item_Type :=
                    Ada_Ent_To_Why.Element
                      (Symbol_Table, Get_Entity_Of_Variable (+Expr));
               begin
                  Insert_Item
                    (I => Item_Type'(Kind     => UCArray,
                                     Content  =>
                                       Binder_Type'(B_Name => Pred_Id,
                                                    others => <>),
                                     Dim      => E.Dim,
                                     Bounds   => E.Bounds),
                     E => Pred_Param);
               end;
            else
               Insert_Entity (Pred_Param, Pred_Id);
            end if;

            --  Transform the predicate expression into Why3

            Result := +Transform_Expr (Expr   => Pred_Expr,
                                       Domain => EW_Pred,
                                       Params => Params);

            --  Relate the name Pred_Id used in the predicate expression to the
            --  value Expr for which the predicate is checked.

            Result := New_Binding (Name    => Pred_Id,
                                   Def     => +Expr,
                                   Context => +Result,
                                   Typ     => Get_Type (+Result));

            Ada_Ent_To_Why.Pop_Scope (Symbol_Table);
         end;
      end if;

      return Result;
   end Compute_Dynamic_Predicate;

   -----------------------
   -- Compute_Tag_Check --
   -----------------------

   function Compute_Tag_Check
     (Call   : Node_Id;
      Params : Transformation_Params) return W_Prog_Id
   is
      Controlling_Arg : constant Node_Id :=
        (if Nkind (Call) = N_Entry_Call_Statement
         then Empty
         else Controlling_Argument (Call));
      Control_Tag     : W_Expr_Id;
      Check           : W_Pred_Id := True_Pred;
      Needs_Check     : Boolean := False;

      procedure One_Arg (Formal, Actual : Node_Id);
         --  Compute a Why expression for each parameter

      -------------
      -- One_Arg --
      -------------

      procedure One_Arg (Formal, Actual : Node_Id) is
         pragma Unreferenced (Formal);
         New_Check : W_Pred_Id;
      begin
         if not Is_Controlling_Actual (Actual)
           or else Actual = Controlling_Arg
         then
            return;
         end if;

         --  We have found a controlling argument different from the first one.
         --  We need a check. If it's the first time we come here, we need to
         --  compute the reference tag first

         if not Needs_Check then
            Needs_Check := True;
            declare
               Tmp : constant W_Expr_Id :=
                 Transform_Expr (Controlling_Arg, EW_Term, Params);
            begin
               Control_Tag :=
                 New_Tag_Access
                   (Ada_Node => Controlling_Arg,
                    Domain   => EW_Term,
                    Name     => Tmp,
                    Ty       => Get_Ada_Node (+Get_Type (Tmp)));
            end;
         end if;
         declare
            Tmp : constant W_Expr_Id :=
              Transform_Expr (Actual, EW_Term, Params);
         begin
            New_Check :=
              New_Call
                (Name => Why_Eq,
                 Typ  => EW_Bool_Type,
                 Args =>
                   (1 => Control_Tag,
                    2 =>
                      New_Tag_Access
                        (Name => Tmp,
                         Ada_Node => Actual,
                         Domain => EW_Term,
                         Ty   => Get_Ada_Node (+Get_Type (Tmp)))));
         end;

         Check :=
           +New_And_Expr
           (Domain => EW_Pred,
            Left   => +Check,
            Right  => +New_Check);
      end One_Arg;

      procedure Iterate_Call is new Iterate_Call_Arguments (One_Arg);

   begin
      if not Present (Controlling_Arg) then
         return New_Void (Call);
      end if;

      Iterate_Call (Call);
      if Needs_Check then
         return
           New_Located_Assert
             (Ada_Node => Call,
              Pred     => Check,
              Reason   => VC_Tag_Check,
              Kind     => EW_Assert);
      else
         return New_Void (Call);
      end if;
   end Compute_Tag_Check;

   --------------------------------------------
   -- Declaration_Is_Associated_To_Parameter --
   --------------------------------------------

   function Declaration_Is_Associated_To_Parameter
     (N : Node_Id) return Boolean
   is
      (Nkind (N) in N_Entity
        and then Ekind (N) in Type_Kind | E_Constant | E_Variable
        and then Present (Related_Expression (N))
        and then Nkind (Related_Expression (N)) in N_Entity
        and then Is_Formal (Related_Expression (N)));

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
            if Is_Type (Entity (Choice)) then
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
         --  The frontend may introduce an unchecked type conversion on the
         --  variable assigned to, in particular for inlining. Reach through
         --  the variable assigned in that case.

         when N_Unchecked_Type_Conversion =>
            return Expected_Type_Of_Prefix (Expression (N));

         when N_Type_Conversion =>
            return Expected_Type_Of_Prefix (Expression (N));

         when N_Identifier | N_Expanded_Name =>
            declare
               Ent : constant Entity_Id := Entity (N);
            begin
               if Is_Protected_Component_Or_Discr (Ent) then
                  return Type_Of_Node (Etype (Ent));
               else
                  return Get_Why_Type_From_Item
                    (Ada_Ent_To_Why.Element (Symbol_Table, Ent));
               end if;
            end;
         when N_Slice =>
            return EW_Abstract (Unique_Entity (Etype (N)));

         when N_Indexed_Component =>
            return EW_Abstract
              (Component_Type (Unique_Entity (Etype (Prefix (N)))));

         when N_Selected_Component =>
            return EW_Abstract (Etype (Selector_Name (N)));

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
      Iter : constant Node_Id := Sinfo.Name (N);
   begin
      return (Iter);
   end Get_Container_In_Iterator_Specification;

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
         Gen_Marker   => False,
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

   -------------------------------
   -- Has_Visibility_On_Refined --
   -------------------------------

   function Has_Visibility_On_Refined
     (Expr : Node_Id;
      E : Entity_Id)
      return Boolean
   is
      Our_Scope : constant Flow_Scope := Get_Flow_Scope (Expr);
   begin
      return Is_Visible (E, Our_Scope);
   end Has_Visibility_On_Refined;

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
                          Name     => E_Symb (Base, WNE_Range_Check_Fun),
                          Progs    => (1 => +T),
                          Reason   => VC_Overflow_Check,
                          Typ      => Get_Type (T));
   end Insert_Overflow_Check;

   ----------------------------
   -- Insert_Predicate_Check --
   ----------------------------

   function Insert_Predicate_Check
     (Ada_Node : Node_Id;
      Check_Ty : Entity_Id;
      W_Expr   : W_Prog_Id;
      Var_Ent  : Entity_Id := Empty) return W_Prog_Id
   is
      W_Tmp : constant W_Identifier_Id :=
        New_Temp_Identifier (Typ      => Get_Type (+W_Expr),
                             Ada_Node => Var_Ent);
      --  If W_Expr is an array in split form, we need to link W_Tmp to Var_Ent
      --  so that the proper bounds can be retrieved.

      W_Seq : constant W_Prog_Id :=
        Sequence (New_Predicate_Check (Ada_Node, Check_Ty, +W_Tmp), +W_Tmp);
   begin
      return +W_Expr_Id'(New_Binding (Ada_Node => Ada_Node,
                                      Domain   => EW_Prog,
                                      Name     => W_Tmp,
                                      Def      => +W_Expr,
                                      Context  => +W_Seq,
                                      Typ      => Get_Type (+W_Expr)));
   end Insert_Predicate_Check;

   ------------------------
   -- Insert_Ref_Context --
   ------------------------

   function Insert_Ref_Context
     (Params     : Transformation_Params;
      Ada_Call   : Node_Id;
      Why_Call   : W_Prog_Id;
      Nb_Of_Refs : Positive;
      Nb_Of_Lets : Natural) return W_Prog_Id
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
      Ref_Index       : Positive := 1;
      Ref_Tmp_Vars    : W_Identifier_Array (1 .. Nb_Of_Refs);
      Ref_Fetch       : W_Prog_Array (1 .. Nb_Of_Refs);
      Let_Index       : Positive := 1;
      Let_Tmp_Vars    : W_Identifier_Array (1 .. Nb_Of_Lets);
      Let_Fetch       : W_Prog_Array (1 .. Nb_Of_Lets);
      Store       : constant W_Statement_Sequence_Unchecked_Id :=
        New_Unchecked_Statement_Sequence;
      Subp        : constant Entity_Id := Entity (Sinfo.Name (Ada_Call));
      Binders     : constant Item_Array :=
        Compute_Subprogram_Parameters (Subp, EW_Prog);
      Bind_Cnt    : Positive := Binders'First;

      procedure Process_Arg (Formal, Actual : Node_Id);

      -----------------
      -- Process_Arg --
      -----------------

      procedure Process_Arg (Formal, Actual : Node_Id) is
      begin
         case Binders (Bind_Cnt).Kind is
            when Prot_Self =>
               null;
            when Regular =>
               if Needs_Temporary_Ref
                 (Actual, Formal, Get_Typ (Binders (Bind_Cnt).Main.B_Name))
               then
                  declare
                     --  Types:

                     Formal_T : constant W_Type_Id :=
                       Get_Typ (Binders (Bind_Cnt).Main.B_Name);
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

                     --  On fetch, checks are only needed when the formal is a
                     --  scalar IN or IN OUT, and potentially always needed for
                     --  composite parameters.

                     Need_Check_On_Fetch : constant Boolean :=
                       (if Is_Scalar_Type (Retysp (Etype (Formal))) then
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
                                                    Expr     =>
                                                      +Prefetch_Actual,
                                                    To       => Formal_T)
                        else
                        +Insert_Simple_Conversion (Ada_Node => Actual,
                                                   Domain   => EW_Prog,
                                                   Expr     =>
                                                     +Prefetch_Actual,
                                                   To       => Formal_T));

                     --  2/ After the call (storing the result):
                     -------------------------------------------

                     --  On store, checks are only needed when the formal is a
                     --  scalar OUT or IN OUT, and never needed for composite
                     --  parameters.

                     Need_Check_On_Store : constant Boolean :=
                       (if Is_Scalar_Type (Retysp (Etype (Formal))) then
                           Ekind (Formal) /= E_In_Parameter
                        else
                           False);

                     --  Generate an expression of the form:
                     --
                     --    to_actual_type_ (from_formal_type (!tmp_var))
                     --
                     --  ... with the appropriate checks if needed.

                     --  if the actual is a type conversion, then in the case
                     --  of the "store" (see point 2 below) we need to undo
                     --  the type conversion, that is do the type conversion in
                     --  the other direction. So we retrieve the type of that
                     --  expression here, and use it also as an Ada_ node.

                     Actual_Target_T : constant W_Type_Id :=
                       (if Nkind (Actual) = N_Type_Conversion then
                             Type_Of_Node (Expression (Actual))
                        else Actual_T);

                     Actual_Target_Node : constant Node_Id :=
                       (if Nkind (Actual) = N_Type_Conversion then
                             Expression (Actual)
                        else Actual);

                     Arg_Value     : constant W_Prog_Id :=
                       (if Need_Check_On_Store then
                           +Insert_Checked_Conversion
                            (Ada_Node => Actual,
                             Ada_Type => Etype (Actual),
                             Domain   => EW_Prog,
                             Expr     => +Tmp_Var_Deref,
                             To       => Actual_Target_T)
                        else
                           +Insert_Simple_Conversion
                             (Ada_Node => Actual_Target_Node,
                              Domain   => EW_Prog,
                              Expr     => +Tmp_Var_Deref,
                              To       => Actual_Target_T));

                     --  ...then store it into the actual:

                     Store_Value   : constant W_Prog_Id :=
                       New_Assignment
                         (Ada_Node => Actual,
                          Lvalue   => Actual,
                          Expr     => Arg_Value);
                  begin
                     Statement_Sequence_Append_To_Statements
                       (Store, Store_Value);

                     Ref_Tmp_Vars (Ref_Index) := Tmp_Var;
                     Ref_Fetch (Ref_Index) := Fetch_Actual;
                     Ref_Index := Ref_Index + 1;
                  end;
               end if;

            when UCArray =>
               if Get_Type_Kind (Type_Of_Node (Actual)) = EW_Abstract
                 or else not (Nkind (Actual) in N_Identifier |
                              N_Expanded_Name)
               then
                  declare
                     --  Types:

                     Formal_T : constant W_Type_Id :=
                       Get_Typ (Binders (Bind_Cnt).Content.B_Name);
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

                     --  If the argument is in split form and not the actual,
                     --  we need to reconstruct the argument using the actual's
                     --  bounds before applying the conversion. To only do the
                     --  actual computation once, we introduce a temporary
                     --  variable for it.

                     Need_Reconstruction : constant Boolean :=
                       Get_Type_Kind (Actual_T) = EW_Abstract;

                  --  1/ Before the call (saving into a temporary variable):
                  ----------------------------------------------------------

                     --  On fetch, checks are potentially always needed for
                     --  composite parameters.

                     --  Generate an expression of the form:
                     --
                     --    to_formal_type (from_actual_type (!actual))
                     --
                     --  ... with the appropriate checks if needed.

                     Prefetch_Actual : constant W_Prog_Id :=
                       +Transform_Expr (Actual,
                                        EW_Prog,
                                        Params);

                     Prefetch_Actual_Tmp : constant W_Identifier_Id :=
                       New_Identifier (Name => Full_Name (Formal) & "__compl",
                                       Typ  => Actual_T);

                     Prefetch_Actual_Rec : constant W_Prog_Id :=
                       (if Need_Reconstruction then +Prefetch_Actual_Tmp
                        else Prefetch_Actual);

                     Fetch_Actual  : constant W_Prog_Id :=
                       +Insert_Checked_Conversion (Ada_Node => Actual,
                                                   Ada_Type => Etype (Actual),
                                                   Domain   => EW_Prog,
                                                   Expr     =>
                                                     +Prefetch_Actual_Rec,
                                                   To       => Formal_T);

                     --  2/ After the call (storing the result):
                     -------------------------------------------

                     --  If the argument is in split form, we
                     --  need to reconstruct the argument using the actual's
                     --  bounds before applying the conversion.

                     Reconstructed_Temp : constant W_Prog_Id :=
                       (if Get_Type_Kind (Formal_T) = EW_Split then
                        +Array_Convert_From_Base
                          (EW_Prog, +Prefetch_Actual_Rec, +Tmp_Var_Deref)
                        else +Tmp_Var_Deref);

                     --  Generate an expression of the form:
                     --
                     --    to_actual_type_ (from_formal_type (!tmp_var))

                     Arg_Value     : constant W_Prog_Id :=
                       +Insert_Simple_Conversion
                       (Ada_Node => Actual,
                        Domain   => EW_Pterm,
                        Expr     => +Reconstructed_Temp,
                        To       => Actual_T);

                     --  ...then store it into the actual:

                     Store_Value   : constant W_Prog_Id :=
                       New_Assignment
                         (Ada_Node => Actual,
                          Lvalue   => Actual,
                          Expr     => Arg_Value);
                  begin

                     Statement_Sequence_Append_To_Statements
                       (Store, Store_Value);

                     Ref_Tmp_Vars (Ref_Index) := Tmp_Var;
                     Ref_Fetch (Ref_Index) := Fetch_Actual;
                     Ref_Index := Ref_Index + 1;

                     if Need_Reconstruction then
                        Let_Tmp_Vars (Let_Index) := Prefetch_Actual_Tmp;
                        Let_Fetch (Let_Index) := Prefetch_Actual;
                        Let_Index := Let_Index + 1;
                     end if;
                  end;
               end if;

            when DRecord =>
               if not (Nkind (Actual) in N_Identifier | N_Expanded_Name
                       and then Eq_Base (EW_Abstract (Binders (Bind_Cnt).Typ),
                                         Type_Of_Node (Actual)))
               then
                  declare
                     Formal_T                : constant W_Type_Id :=
                       EW_Abstract (Binders (Bind_Cnt).Typ);
                     Actual_T                : constant W_Type_Id :=
                       Type_Of_Node (Actual);

                     Actual_Is_Split         : constant Boolean :=
                       Nkind (Actual) in N_Identifier | N_Expanded_Name;
                     --  The actual is split if and only if it is an
                     --  identifier.

                     --  1/ Before the call (saving into temporary variables):
                     ----------------------------------------------------------

                     Prefetch_Actual_Tmp     : constant W_Identifier_Id :=
                       New_Identifier (Name => Full_Name (Formal) & "__compl",
                                       Typ  => Formal_T);
                     --  Temporary variable to hold the value of the converted
                     --  actual if it cannot be used as is.

                     Prefetch_Actual         : constant W_Prog_Id :=
                       +Transform_Expr (Actual, Formal_T, EW_Prog, Params);

                     Needs_Ref_For_Fields    : constant Boolean :=
                       Binders (Bind_Cnt).Fields.Present;
                     --  We need a new reference for the fields whenever there
                     --  is at least one field.

                     Tmp_Var_For_Fields      : W_Identifier_Id;
                     --  Variable for the reference for fields

                     Fetch_Actual_For_Fields : constant W_Prog_Id :=
                       +New_Fields_Access (Domain => EW_Prog,
                                           Name   => +Prefetch_Actual_Tmp,
                                           Ty     => Binders (Bind_Cnt).Typ);

                     Needs_Ref_For_Discrs    : Boolean := False;

                     Tmp_Var_For_Discrs      : W_Identifier_Id;
                     --  Variable for the reference for discriminants

                     Fetch_Actual_For_Discrs : W_Prog_Id;

                     --  2/ After the call (storing the result):
                     -------------------------------------------

                     Reconstructed_Arg       : W_Prog_Id;

                     Assumption              : W_Expr_Id;
                     --  If the actual has non mutable discriminants, we need
                     --  to assume that its discriminants have not been
                     --  modified.

                  begin
                     --  We initialize the remaining elements of the first
                     --  phase.

                     if Needs_Ref_For_Fields then
                        Tmp_Var_For_Fields :=
                          New_Identifier
                            (Ada_Node => Empty,
                             Name     => Full_Name (Formal) & "__fields",
                             Typ      =>
                               Get_Typ
                                 (Binders (Bind_Cnt).Fields.Binder.B_Name));
                     end if;

                     if Binders (Bind_Cnt).Discrs.Present
                       and then Binders (Bind_Cnt).Discrs.Binder.Mutable
                     then
                        --  We need a new reference for the discriminants
                        --  whenever there is at least one discriminant, the
                        --  formal has mutable discriminants and we cannot use
                        --  the discriminant reference of the actual directly
                        --  the actual is not split or it has constant (ie.
                        --  discriminants).

                        if Actual_Is_Split then
                           declare
                              Actual_Binder : constant Item_Type :=
                                Ada_Ent_To_Why.Element
                                  (Symbol_Table, Entity (Actual));
                           begin

                              Needs_Ref_For_Discrs :=
                                not Actual_Binder.Discrs.Binder.Mutable;

                              --  If the actual is in split form and its
                              --  discriminants are not mutable, use them to
                              --  initialize Tmp_Var_For_Discrs.

                              Fetch_Actual_For_Discrs :=
                                +Actual_Binder.Discrs.Binder.B_Name;
                           end;
                        else

                           Needs_Ref_For_Discrs := True;

                           --  If the actual is not in split form, use the
                           --  constant introduced for the actual to avoid
                           --  recomputing it.

                           Fetch_Actual_For_Discrs :=
                             +New_Discriminants_Access
                             (Domain => EW_Prog,
                              Name   => +Prefetch_Actual_Tmp,
                              Ty     => Binders (Bind_Cnt).Typ);
                        end if;

                        Tmp_Var_For_Discrs :=
                          New_Identifier
                            (Ada_Node => Empty,
                             Name     => Full_Name (Formal) & "__discrs",
                             Typ      =>
                               Get_Typ
                                 (Binders (Bind_Cnt).Discrs.Binder.B_Name));
                     end if;

                     --  We reconstruct the argument and convert it to the
                     --  actual type (without checks). We store the result in
                     --  Reconstructed_Arg.

                     --  We reconstruct the argument, convert it to the
                     --  actual type (without checks), and assign it to the
                     --  actual.

                     --  ??? WHY repetition above?

                     declare
                        Arg_Array  : W_Expr_Array (1 .. 4);
                        Index      : Positive := 1;
                     begin

                        --  For fields, use the temporary variable.

                        if Binders (Bind_Cnt).Fields.Present then
                           Arg_Array (Index) :=
                             New_Deref (Right => Tmp_Var_For_Fields,
                                        Typ   =>
                                          Get_Typ (Tmp_Var_For_Fields));
                           Index := Index + 1;
                        end if;

                        if Binders (Bind_Cnt).Discrs.Present then
                           if Actual_Is_Split then

                              --  If the actual is split, we can use its
                              --  discriminants directly since we must have
                              --  already updated them if they were mutable.

                              declare
                                 Actual_Binder : constant Item_Type :=
                                   Ada_Ent_To_Why.Element
                                     (Symbol_Table, Entity (Actual));
                                 Discrs        : constant W_Identifier_Id :=
                                   Actual_Binder.Discrs.Binder.B_Name;
                              begin
                                 if Actual_Binder.Discrs.Binder.Mutable then
                                    Arg_Array (Index) :=
                                      New_Deref (Right => Discrs,
                                                 Typ   => Get_Typ (Discrs));
                                 else
                                    Arg_Array (Index) := +Discrs;
                                 end if;
                              end;
                           elsif Binders (Bind_Cnt).Discrs.Binder.Mutable
                           then
                              Arg_Array (Index) :=
                                New_Deref (Right => Tmp_Var_For_Discrs,
                                           Typ   =>
                                             Get_Typ (Tmp_Var_For_Discrs));
                           else
                              Arg_Array (Index) :=
                                New_Discriminants_Access
                                  (Domain => EW_Prog,
                                   Name   => +Prefetch_Actual_Tmp,
                                   Ty     => Binders (Bind_Cnt).Typ);
                           end if;

                           Index := Index + 1;
                        end if;

                        --  If the formal has mutable discriminants, store
                        --  in Assumption that its discriminants cannot have
                        --  been modified if the actual is constrained.

                        if Needs_Ref_For_Discrs then
                           Assumption :=
                             New_Call
                               (Domain => EW_Pred,
                                Typ    => EW_Bool_Type,
                                Name   => Why_Eq,
                                Args =>
                                  (1 => New_Deref (Right => Tmp_Var_For_Discrs,
                                                   Typ   =>
                                                     Get_Typ
                                                       (Tmp_Var_For_Discrs)),
                                   2 => +Fetch_Actual_For_Discrs));

                           Assumption :=
                             New_Conditional
                               (Domain      => EW_Pred,
                                Condition   =>
                                  New_Is_Constrained_Access
                                    (Domain   => EW_Term,
                                     Name     => +Prefetch_Actual_Tmp,
                                     Ty       => Binders (Bind_Cnt).Typ),
                                Then_Part   => Assumption);
                        end if;

                        if Binders (Bind_Cnt).Constr.Present then
                           Arg_Array (Index) :=
                             New_Is_Constrained_Access
                               (Domain => EW_Prog,
                                Name   => +Prefetch_Actual_Tmp,
                                Ty     => Binders (Bind_Cnt).Typ);

                           Index := Index + 1;
                        end if;

                        if Binders (Bind_Cnt).Tag.Present then
                           Arg_Array (Index) :=
                             New_Tag_Access
                               (Domain => EW_Prog,
                                Name   => +Prefetch_Actual_Tmp,
                                Ty     => Binders (Bind_Cnt).Typ);

                           Index := Index + 1;
                        end if;

                        Reconstructed_Arg :=
                          +Record_From_Split_Form
                            (A  => Arg_Array (1 .. Index - 1),
                             Ty => Binders (Bind_Cnt).Typ);

                        Reconstructed_Arg :=
                          +Insert_Simple_Conversion
                            (Domain   => EW_Pterm,
                             Expr     => +Reconstructed_Arg,
                             To       => Actual_T);
                     end;

                     --  Store the assignment, the assumption, and the required
                     --  declarations.

                     Statement_Sequence_Append_To_Statements
                       (Store, New_Assignment
                          (Ada_Node => Actual,
                           Lvalue   => Actual,
                           Expr     => Reconstructed_Arg));

                     if Needs_Ref_For_Discrs then
                        Statement_Sequence_Append_To_Statements
                          (Store, New_Assume_Statement (Pred => +Assumption));
                     end if;

                     if Needs_Ref_For_Fields then
                        Ref_Tmp_Vars (Ref_Index) := Tmp_Var_For_Fields;
                        Ref_Fetch (Ref_Index) := Fetch_Actual_For_Fields;
                        Ref_Index := Ref_Index + 1;
                     end if;

                     if Needs_Ref_For_Discrs then
                        Ref_Tmp_Vars (Ref_Index) := Tmp_Var_For_Discrs;
                        Ref_Fetch (Ref_Index) := Fetch_Actual_For_Discrs;
                        Ref_Index := Ref_Index + 1;
                     end if;

                     Let_Tmp_Vars (Let_Index) := Prefetch_Actual_Tmp;
                     Let_Fetch (Let_Index) := Prefetch_Actual;
                     Let_Index := Let_Index + 1;
                  end;
               end if;
            when Func    => raise Program_Error;
         end case;

         --  If needed, perform the check for a dynamic predicate on OUT and
         --  IN OUT parameters on return from the call. This check is not done
         --  as part of the conversion from formal to actual parameter, as
         --  the check done in conversions also involves invariant properties
         --  of the type (array bounds, record discriminants, etc.). Thus,
         --  conversion is done with Insert_Simple_Conversion in domain
         --  EW_Pterm, which does not introduce checks, and the required
         --  check for dynamic predicate is introduced here.

         --  The case of scalar types is different, as the conversion from
         --  formal to actual on OUT and IN OUT parameters is performed with
         --  checks, using Insert_Checked_Conversion in domain EW_Prog, so do
         --  not repeat the check here.

         declare
            Need_Pred_Check_On_Store : constant Boolean :=
              not Is_Scalar_Type (Retysp (Etype (Formal)))
              and then Ekind (Formal) /= E_In_Parameter
              and then
                not Eq_Base (Type_Of_Node (Formal), Type_Of_Node (Actual));
         begin
            if Has_Predicates (Etype (Actual))
              and then Need_Pred_Check_On_Store
            then
               declare
                  Postfetch_Actual : constant W_Prog_Id :=
                    +Transform_Expr (Actual, EW_Pterm, Params);
               begin
                  Statement_Sequence_Append_To_Statements
                    (Store, New_Predicate_Check (Actual, Etype (Actual),
                                                 +Postfetch_Actual));
               end;
            end if;
         end;

         Bind_Cnt := Bind_Cnt + 1;
      end Process_Arg;

      procedure Iterate_Call is new
        Iterate_Call_Arguments (Process_Arg);

   --  Start of processing for Insert_Ref_Context

   begin
      Statement_Sequence_Append_To_Statements (Store, Why_Call);
      Iterate_Call (Ada_Call);

      --  Set the pieces together

      Ref_Context := +Store;
      for J in Ref_Fetch'Range loop
         Ref_Context :=
           New_Binding_Ref
             (Name    => Ref_Tmp_Vars (J),
              Def     => Ref_Fetch (J),
              Context => Ref_Context,
              Typ     => Get_Typ (Ref_Tmp_Vars (J)));
      end loop;

      for J in Let_Fetch'Range loop
         Ref_Context :=
              +New_Typed_Binding
                (Domain   => EW_Prog,
                 Name     => Let_Tmp_Vars (J),
                 Def      => +Let_Fetch (J),
                 Context  => +Ref_Context);
      end loop;

      return Ref_Context;
   end Insert_Ref_Context;

   ----------------------
   -- Is_Terminal_Node --
   ----------------------

   function Is_Terminal_Node (N : Node_Id) return Boolean is
   begin
      case Nkind (N) is
         when N_Quantified_Expression | N_And_Then |
              N_Op_And | N_If_Expression
            => return False;
         when others => return True;
      end case;
   end Is_Terminal_Node;

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
               Typ := Type_Of_Node (Etype (Expr));
            end if;
            Loop_Map.Include
              (Expr,
               New_Temp_Identifier
                 (Typ      => Typ,
                  Ada_Node => Nd));
         end if;

         Result := Loop_Map.Element (Expr);
      end Get_Name;

   --  Start of processing for Name_For_Loop_Entry

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
            Typ := Type_Of_Node (Etype (N));
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
     (Actual     : Node_Id;
      Formal     : Node_Id;
      Typ_Formal : W_Type_Id) return Boolean is
   begin
      --  Temporary refs are needed for out or in out parameters that
      --  need a conversion or who are not an identifier.
      case Ekind (Formal) is
         when E_In_Out_Parameter | E_Out_Parameter =>
            return not Eq_Base (Type_Of_Node (Etype (Actual)), Typ_Formal)
              or else not (Nkind (Actual) in N_Identifier | N_Expanded_Name);
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
        (N    : in out Node_Id;
         Expr : in out W_Prog_Id);
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
        (N    : in out Node_Id;
         Expr : in out W_Prog_Id) is
      begin
         case Nkind (N) is
            when N_Identifier | N_Expanded_Name =>
               null;

            when N_Type_Conversion | N_Unchecked_Type_Conversion =>
                  N := Expression (N);
                  Expr :=
                    +Insert_Simple_Conversion
                      (Domain => EW_Prog,
                       Expr   => +Expr,
                       To     => Type_Of_Node (Etype (N)));

            when N_Selected_Component | N_Indexed_Component | N_Slice =>
               declare
                  Prefix_Type : constant W_Type_Id :=
                    Expected_Type_Of_Prefix (Prefix (N));

                  --  We compute the expression for the Prefix in the EW_Term
                  --  domain so that checks are not done for it as they are
                  --  duplicates of those done in One_Level_Update.

                  Prefix_Expr : constant W_Expr_Id :=
                    +Transform_Expr (Domain        => EW_Pterm,
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
               Ada.Text_IO.Put_Line ("[Shift_Rvalue] kind ="
                                     & Node_Kind'Image (Nkind (N)));
               raise Not_Implemented;
         end case;
      end Shift_Rvalue;

      Left_Side  : Node_Id   := Lvalue;
      Right_Side : W_Prog_Id := Expr;
      Result     : W_Prog_Id;

   --  Start of processing for New_Assignment

   begin
      --  Record attributes of objects are not modified by assignments

      declare
         Ty : constant Entity_Id := Etype (Lvalue);
      begin
         if Has_Record_Type (Ty) or else Full_View_Not_In_SPARK (Ty) then
            Right_Side :=
              +New_Record_Attributes_Update
              (Ada_Node  => Ada_Node,
               Domain    => EW_Prog,
               Name      => +Right_Side,
               From_Expr => Transform_Expr (Left_Side, EW_Pterm, Body_Params),
               Ty        => Ty);
         end if;
      end;

      while not (Nkind (Left_Side) in N_Identifier | N_Expanded_Name) loop
         Shift_Rvalue (Left_Side, Right_Side);
      end loop;

      --  in the case of protected components, we have to generate the record
      --  code ourselves on top

      if Is_Protected_Component_Or_Discr_Or_Part_Of (Entity (Left_Side)) then
         declare
            Left : constant Node_Id := Entity (Left_Side);
            Ada_Obj : constant Node_Id :=
              (if Is_Part_Of_Protected_Object (Left) then
                    Get_Enclosing_Concurrent_Object (Left)
               else Empty);
            Prot_Obj : constant W_Identifier_Id :=
              (if Is_Part_Of_Protected_Object (Left) then
                  To_Why_Id
                 (E      => Ada_Obj,
                  Domain => EW_Prog,
                  Typ    => Type_Of_Node (Etype (Ada_Obj)))
               else Self_Name);
         begin
            Result :=
              New_Assignment
                (Ada_Node => Ada_Node,
                 Name     => Prot_Obj,
                 Value    =>
                   +One_Level_Update
                   (Left_Side,
                    New_Deref (Right => +Prot_Obj,
                               Typ   => Get_Typ (Prot_Obj)),
                    +Right_Side,
                    EW_Prog,
                    Body_Params),
                 Typ     => Get_Typ (Prot_Obj));
         end;
      else
         declare
            Binder : constant Item_Type :=
              Ada_Ent_To_Why.Element (Symbol_Table, Entity (Left_Side));
         begin
            case Binder.Kind is
            when Regular =>
               Result :=
                 New_Assignment
                   (Ada_Node => Ada_Node,
                    Name     => Binder.Main.B_Name,
                    Value    => Right_Side,
                    Typ      => Get_Typ (Binder.Main.B_Name));

            when UCArray =>
               Result :=
                 New_Assignment
                   (Ada_Node => Ada_Node,
                    Name     => Binder.Content.B_Name,
                    Value    => Right_Side,
                    Typ      => Get_Typ (Binder.Content.B_Name));

            when DRecord =>
               declare
                  Tmp : constant W_Expr_Id := New_Temp_For_Expr (+Right_Side);
               begin
                  Result := New_Void;

                  if Binder.Fields.Present then
                     Result := New_Assignment
                       (Ada_Node => Ada_Node,
                        Name     => Binder.Fields.Binder.B_Name,
                        Value    => +New_Fields_Access
                          (Domain   => EW_Prog,
                           Name     => Tmp,
                           Ty       => Binder.Typ),
                        Typ      => Get_Typ (Binder.Fields.Binder.B_Name));
                  end if;

                  if Binder.Discrs.Present then
                     if Binder.Discrs.Binder.Mutable then
                        Result := Sequence
                          (Result, New_Assignment
                             (Ada_Node => Ada_Node,
                              Name     => Binder.Discrs.Binder.B_Name,
                              Value    => +New_Discriminants_Access
                                (Domain   => EW_Prog,
                                 Name     => Tmp,
                                 Ty       => Binder.Typ),
                              Typ      =>
                                Get_Typ (Binder.Discrs.Binder.B_Name)));
                     else
                        Result := Sequence
                          (Result, New_Assume_Statement
                             (Ada_Node => Ada_Node,
                              Pred     => +New_Comparison
                                (Symbol => Why_Eq,
                                 Left   => +Binder.Discrs.Binder.B_Name,
                                 Right  => +New_Discriminants_Access
                                   (Domain   => EW_Term,
                                    Name     => Tmp,
                                    Ty       => Binder.Typ),
                                 Domain => EW_Pred)));
                     end if;
                  end if;

                  Result := +Binding_For_Temp (Ada_Node => Ada_Node,
                                               Domain   => EW_Prog,
                                               Tmp      => Tmp,
                                               Context  => +Result);
               end;

            when Func | Prot_Self =>
               raise Program_Error;
            end case;
         end;
      end if;

      return Result;
   end New_Assignment;

   -----------------
   -- New_Op_Expr --
   -----------------

   function New_Op_Expr
     (Op          : N_Op;
      Left        : W_Expr_Id := Why_Empty;
      Right       : W_Expr_Id;
      Left_Type   : Entity_Id := Empty;
      Right_Type  : Entity_Id;
      Return_Type : Entity_Id;
      Domain      : EW_Domain;
      Ada_Node    : Node_Id := Empty) return W_Expr_Id
   is
      T : W_Expr_Id;

   begin
      case Op is
         when N_Op_Compare =>

            --  special case for equality between Booleans in predicates

            if Domain = EW_Pred and then
              Op = N_Op_Eq and then
              Is_Standard_Boolean_Type (Left_Type)
            then
               T :=
                 New_Connection
                   (Domain => EW_Pred,
                    Left   => Insert_Simple_Conversion
                      (Ada_Node => Ada_Node,
                       Domain   => EW_Pred,
                       Expr     => Left,
                       To       => EW_Bool_Type),
                    Right  => Insert_Simple_Conversion
                      (Ada_Node => Ada_Node,
                       Domain   => EW_Pred,
                       Expr     => Right,
                       To       => EW_Bool_Type),
                    Op     => EW_Equivalent);

            elsif Is_Array_Type (Left_Type)
              and then Op in N_Op_Eq | N_Op_Ne
            then
               T := Transform_Array_Equality
                 (Op        => Op,
                  Left      => Left,
                  Right     => Right,
                  Left_Type => Left_Type,
                  Domain    => Domain,
                  Ada_Node  => Ada_Node);
            elsif Is_Array_Type (Left_Type) then
               T := Transform_Array_Comparison
                 (Op        => Op,
                  Left      => Left,
                  Right     => Right,
                  Domain    => Domain,
                  Ada_Node  => Ada_Node);
            else
               declare
                  Subdomain : constant EW_Domain :=
                    (if Domain = EW_Pred then EW_Term else Domain);

                  BT        : constant W_Type_Id :=
                    Base_Why_Type (Left_Type, Right_Type);

               begin
                  if Has_Record_Type (Left_Type)
                    or else Full_View_Not_In_SPARK (Left_Type)
                  then
                     pragma Assert (Root_Record_Type (Left_Type) =
                                      Root_Record_Type (Right_Type));
                     pragma Assert (Root_Record_Type (Left_Type) =
                                      Root_Record_Type (Get_Ada_Node (+BT)));

                     if Is_Class_Wide_Type (Left_Type) then

                        --  Dispatching equality. Translate to:
                        --  let a = to_root left in
                        --  let b = to_root right in
                        --    a.attr_tag = b.attr_tag /\
                        --    __dispatch_eq a b

                        declare
                           Root : constant Entity_Id :=
                             Root_Record_Type (Left_Type);
                           Args : constant W_Expr_Array :=
                             (1 => New_Temp_For_Expr
                                (Insert_Simple_Conversion
                                     (Ada_Node => Ada_Node,
                                      Domain   => Subdomain,
                                      Expr     => Left,
                                      To       => Type_Of_Node (Root))),
                              2 => New_Temp_For_Expr
                                (Insert_Simple_Conversion
                                     (Ada_Node => Ada_Node,
                                      Domain   => Subdomain,
                                      Expr     => Right,
                                      To       => Type_Of_Node (Root))));
                        begin
                           T := New_And_Then_Expr
                             (Left   => New_Call
                                (Ada_Node => Ada_Node,
                                 Domain   => Subdomain,
                                 Name     => Why_Eq,
                                 Args     =>
                                   (1 => New_Tag_Access
                                        (Domain   => Subdomain,
                                         Name     => Args (1),
                                         Ty       => Root),
                                    2 => New_Tag_Access
                                      (Domain   => Subdomain,
                                       Name     => Args (2),
                                       Ty       => Root)),
                                 Typ      => EW_Bool_Type),
                              Right  =>
                                New_Call
                                  (Ada_Node => Ada_Node,
                                   Domain   => Subdomain,
                                   Name     =>
                                     E_Symb (Root, WNE_Dispatch_Eq),
                                   Args     => Args,
                                   Typ      => EW_Bool_Type),
                              Domain => Subdomain);

                           T := Binding_For_Temp (Domain   => Subdomain,
                                                  Tmp      => Args (1),
                                                  Context  => T);
                           T := Binding_For_Temp (Domain   => Subdomain,
                                                  Tmp      => Args (2),
                                                  Context  => T);
                        end;
                     else
                        T :=
                          New_Call
                            (Ada_Node => Ada_Node,
                             Domain   => Subdomain,
                             Name     =>
                               E_Symb (Get_Ada_Node (+BT), WNE_Bool_Eq),
                             Args     => (1 => Insert_Simple_Conversion
                                          (Ada_Node => Ada_Node,
                                           Domain   => Subdomain,
                                           Expr     => Left,
                                           To       => BT),
                                          2 => Insert_Simple_Conversion
                                            (Ada_Node => Ada_Node,
                                             Domain   => Subdomain,
                                             Expr     => Right,
                                             To       => BT)),
                             Typ      => EW_Bool_Type);
                     end if;

                     if Domain = EW_Pred then
                        T := New_Comparison
                          (Symbol =>
                             Transform_Compare_Op (Op, EW_Bool_Type, Domain),
                           Left   => T,
                           Right  => New_Literal (Domain => Subdomain,
                                                  Value  => EW_True),
                           Domain => Domain);

                     elsif Op = N_Op_Ne then
                        T :=
                          New_Call (Domain => Domain,
                                    Name   => M_Boolean.Notb,
                                    Args   => (1 => T),
                                    Typ    => EW_Bool_Type);
                     end if;
                  else
                     T := New_Comparison
                       (Symbol    => Transform_Compare_Op (Op, BT, Domain),
                        Left      => Insert_Simple_Conversion
                          (Ada_Node => Ada_Node,
                           Domain   => Domain,
                           Expr     => Left,
                           To       => BT),
                        Right     => Insert_Simple_Conversion
                          (Ada_Node => Ada_Node,
                           Domain   => Domain,
                           Expr     => Right,
                           To       => BT),
                        Domain    => Domain);
                  end if;
               end;
            end if;

         when N_Op_Minus =>

            --  unary minus

            declare
               Typ : constant W_Type_Id := Base_Why_Type (Right_Type);

               Minus_Ident : constant W_Identifier_Id :=
                 (if Typ = EW_Int_Type then
                    Int_Unary_Minus
                  elsif Why_Type_Is_BitVector (Typ) then
                    MF_BVs (Typ).Neg
                  elsif Typ = EW_Fixed_Type then
                    Fixed_Unary_Minus
                  else Real_Unary_Minus);

               Right_Rep : constant W_Expr_Id := Insert_Simple_Conversion
                 (Ada_Node => Ada_Node,
                  Domain   => Domain,
                  Expr     => Right,
                  To       => Typ);

            begin
               if Has_Modular_Integer_Type (Return_Type)
                 and then Non_Binary_Modulus (Return_Type)
               then
                  T := Transform_Non_Binary_Modular_Operation
                    (Ada_Node   => Ada_Node,
                     Ada_Type   => Return_Type,
                     Domain     => Domain,
                     Op         => N_Op_Minus,
                     Right_Opnd => Right_Rep,
                     Rep_Type   => Typ,
                     Modulus    => Modulus (Return_Type));

               else
                  T :=
                    New_Call
                      (Domain   => Domain,
                       Ada_Node => Ada_Node,
                       Name     => Minus_Ident,
                       Args     =>
                         (1 => Right_Rep),
                       Typ       => Get_Type (+Minus_Ident));
                  T := Apply_Modulus_Or_Rounding (Op, Return_Type, T, Domain);
               end if;
            end;

         when N_Op_Plus =>

            --  unary plus

            T := Right;

         when N_Op_Abs =>
            declare
               Typ   : constant W_Type_Id := Base_Why_Type (Right_Type);
            begin
               T :=
                 New_Call
                   (Ada_Node => Ada_Node,
                    Domain   => Domain,
                    Name     => New_Abs (Typ),
                    Args     => (1 => Insert_Simple_Conversion
                                 (Ada_Node => Ada_Node,
                                  Domain   => Domain,
                                  Expr     => Right,
                                  To       => Base_Why_Type (Right_Type))),
                    Typ     => Typ);
            end;

         when N_Op_Add | N_Op_Subtract =>
            --  The arguments of arithmetic functions have to be of base
            --  scalar types
            declare
               Base : constant W_Type_Id :=
                 Base_Why_Type (Left_Type, Right_Type);
               Name : constant W_Identifier_Id :=
                 (if Op = N_Op_Add then
                    (if Base = EW_Int_Type then Int_Infix_Add
                     elsif Why_Type_Is_BitVector (Base) then
                       MF_BVs (Base).Add
                     elsif Base = EW_Fixed_Type then Fixed_Infix_Add
                     else Real_Infix_Add)
                  else
                    (if Base = EW_Int_Type then Int_Infix_Subtr
                     elsif Why_Type_Is_BitVector (Base) then
                          MF_BVs (Base).Sub
                     elsif Base = EW_Fixed_Type then Fixed_Infix_Subtr
                     else Real_Infix_Subtr));
               Left_Rep : constant W_Expr_Id :=
                 Insert_Simple_Conversion (Ada_Node => Ada_Node,
                                           Domain   => Domain,
                                           Expr     => Left,
                                           To       => Base);
               Right_Rep : constant W_Expr_Id :=
                 Insert_Simple_Conversion (Ada_Node => Ada_Node,
                                           Domain   => Domain,
                                           Expr     => Right,
                                           To       => Base);

            begin
               if Has_Modular_Integer_Type (Return_Type)
                 and then Non_Binary_Modulus (Return_Type)
               then
                  T := Transform_Non_Binary_Modular_Operation
                    (Ada_Node   => Ada_Node,
                     Ada_Type   => Return_Type,
                     Domain     => Domain,
                     Op         => Op,
                     Left_Opnd  => Left_Rep,
                     Right_Opnd => Right_Rep,
                     Rep_Type   => Base,
                     Modulus    => Modulus (Return_Type));

               else
                  T :=
                    New_Call
                      (Ada_Node => Ada_Node,
                       Domain   => Domain,
                       Name     => Name,
                       Args     => (1 => Left_Rep,
                                    2 => Right_Rep),
                       Typ   => Base);
                  T := Apply_Modulus_Or_Rounding (Op, Return_Type, T, Domain);
               end if;
            end;

         when N_Op_Multiply =>
            --  The arguments of arithmetic functions have to be of base
            --  scalar types
            declare
               L_Why : W_Expr_Id := Left;
               R_Why : W_Expr_Id := Right;
               L_Type, R_Type : W_Type_Id;
               Base : W_Type_Id;
               Oper : Why_Name_Enum;
            begin
               if Has_Fixed_Point_Type (Left_Type)
                 and then Has_Fixed_Point_Type (Right_Type)
               then
                  L_Type := EW_Fixed_Type;
                  R_Type := EW_Fixed_Type;
                  Base := EW_Fixed_Type;
                  Oper := WNE_Fixed_Point_Mult;

               elsif Has_Fixed_Point_Type (Left_Type) then
                  L_Type := EW_Fixed_Type;
                  R_Type := EW_Int_Type;
                  Base := EW_Fixed_Type;
                  Oper := WNE_Fixed_Point_Mult_Int;

                  --  If multiplying an integer and a fixed-point, swap
                  --  arguments so that Left is the fixed-point one.

               elsif Has_Fixed_Point_Type (Right_Type) then
                  L_Type := EW_Fixed_Type;
                  R_Type := EW_Int_Type;
                  L_Why := Right;
                  R_Why := Left;
                  Base := EW_Fixed_Type;
                  Oper := WNE_Fixed_Point_Mult_Int;

               else
                  Base := Base_Why_Type (Left_Type, Right_Type);
                  L_Type := Base;
                  R_Type := Base;
               end if;

               L_Why := Insert_Simple_Conversion
                 (Ada_Node => Ada_Node,
                  Domain   => Domain,
                  Expr     => L_Why,
                  To       => L_Type);
               R_Why := Insert_Simple_Conversion
                 (Ada_Node => Ada_Node,
                  Domain   => Domain,
                  Expr     => R_Why,
                  To       => R_Type);

               if Is_Fixed_Point_Type (Return_Type) then
                  T := New_Call (Ada_Node => Ada_Node,
                                 Domain   => Domain,
                                 Name     => E_Symb (Return_Type, Oper),
                                 Args     => (1 => L_Why,
                                              2 => R_Why),
                                 Typ      => Base);

               elsif Has_Modular_Integer_Type (Return_Type)
                 and then Non_Binary_Modulus (Return_Type)
               then
                  T := Transform_Non_Binary_Modular_Operation
                    (Ada_Node   => Ada_Node,
                     Ada_Type   => Return_Type,
                     Domain     => Domain,
                     Op         => Op,
                     Left_Opnd  => L_Why,
                     Right_Opnd => R_Why,
                     Rep_Type   => Base,
                     Modulus    => Modulus (Return_Type));

               else
                  declare
                     Name : constant W_Identifier_Id :=
                       (if Base = EW_Int_Type then Int_Infix_Mult
                        elsif Why_Type_Is_BitVector (Base) then
                          MF_BVs (Base).Mult
                        elsif Base = EW_Fixed_Type then Fixed_Infix_Mult
                        else Real_Infix_Mult);
                  begin
                     T :=
                       New_Call
                         (Ada_Node => Ada_Node,
                          Domain   => Domain,
                          Name     => Name,
                          Args     => (1 => L_Why, 2 => R_Why),
                          Typ      => Base);
                  end;
                  T := Apply_Modulus_Or_Rounding (Op, Return_Type, T, Domain);
               end if;
            end;

         when N_Op_Divide =>
            declare
               Base  : W_Type_Id;
               Oper : Why_Name_Enum;
               Name : W_Identifier_Id;
               L_Type, R_Type : W_Type_Id;
               L_Why, R_Why : W_Expr_Id;
            begin
               if Has_Fixed_Point_Type (Left_Type)
                 and then Has_Fixed_Point_Type (Right_Type)
               then
                  L_Type := EW_Fixed_Type;
                  R_Type := EW_Fixed_Type;

                  case Ekind (Return_Type) is
                     when Fixed_Point_Kind =>
                        Oper := WNE_Fixed_Point_Div;
                        Base := EW_Fixed_Type;

                     when Integer_Kind =>
                        Oper := WNE_Fixed_Point_Div_Result_Int;
                        Base := EW_Int_Type;

                     when others =>
                        raise Program_Error;

                  end case;

               elsif Has_Fixed_Point_Type (Left_Type) then
                  L_Type := EW_Fixed_Type;
                  R_Type := EW_Int_Type;
                  Base := EW_Fixed_Type;
                  Oper := WNE_Fixed_Point_Div_Int;

               else
                  Base := Base_Why_Type (Left_Type, Right_Type);
                  L_Type := Base;
                  R_Type := Base;
               end if;

               Name :=
                 (if Is_Fixed_Point_Type (Return_Type) then
                     E_Symb (Return_Type, Oper)
                  --  Explicit support for division of a fixed point type
                  --  by its small with integer result
                  elsif Has_Fixed_Point_Type (Left_Type)
                    and then Oper = WNE_Fixed_Point_Div_Result_Int
                  then
                     E_Symb (Left_Type, Oper)
                  else
                     New_Division (Base));

               L_Why := Insert_Simple_Conversion
                 (Ada_Node => Ada_Node,
                  Domain   => Domain,
                  Expr     => Left,
                  To       => L_Type);
               R_Why := Insert_Simple_Conversion
                 (Ada_Node => Ada_Node,
                  Domain   => Domain,
                  Expr     => Right,
                  To       => R_Type);

               if Domain = EW_Prog
                 and then Present (Ada_Node)
                 and then Do_Division_Check (Ada_Node)
               then
                  T :=
                    New_VC_Call
                      (Ada_Node => Ada_Node,
                       Domain   => Domain,
                       Name     => To_Program_Space (Name),
                       Progs    => (1 => L_Why, 2 => R_Why),
                       Reason   => VC_Division_Check,
                       Typ      => Base);
               else
                  T :=
                    New_Call
                      (Ada_Node => Ada_Node,
                       Domain   => Domain,
                       Name     => Name,
                       Args     => (1 => L_Why, 2 => R_Why),
                       Typ      => Base);
               end if;

               T := Apply_Modulus_Or_Rounding (Op, Return_Type, T, Domain);
            end;

         when N_Op_Rem | N_Op_Mod =>
            declare
               Base  : constant W_Type_Id :=
                 Base_Why_Type (Left_Type, Right_Type);
               Name  : W_Identifier_Id;
            begin
               Name := (if Why_Type_Is_BitVector (Base) then
                          MF_BVs (Base).Urem
                        elsif Op = N_Op_Rem then
                          M_Int_Div.Rem_Id
                        else M_Int_Div.Mod_Id);

               Name := (if Domain = EW_Prog then
                          To_Program_Space (Name)
                        else
                          Name);
               T :=
                 New_VC_Call
                   (Ada_Node => Ada_Node,
                    Domain   => Domain,
                    Name     => Name,
                    Progs    =>
                      (1 => Insert_Simple_Conversion
                         (Ada_Node => Ada_Node,
                          Domain   => Domain,
                          Expr     => Left,
                          To       => Base),
                       2 => Insert_Simple_Conversion
                         (Ada_Node => Ada_Node,
                          Domain   => Domain,
                          Expr     => Right,
                          To       => Base)),
                    Reason   => VC_Division_Check,
                    Typ      => Base);
            end;

         when N_Op_Expon =>
            declare
               Name    : W_Identifier_Id;
               Typ     : constant W_Type_Id := Base_Why_Type (Left_Type);
            begin
               Name := New_Exp (Typ);

               T := New_Call
                 (Ada_Node => Ada_Node,
                  Domain   => Domain,
                  Name     => Name,
                  Args     =>
                    (1 => Insert_Simple_Conversion
                         (Ada_Node => Ada_Node,
                          Domain   => Domain,
                          Expr     => Left,
                          To       => Typ),
                     2 => Insert_Simple_Conversion
                       (Ada_Node => Ada_Node,
                        Domain   => Domain,
                        Expr     => Right,
                        To       => EW_Int_Type)),
                  Typ      => Typ);

            end;

         when N_Op_Not =>
            if Is_Array_Type (Right_Type) then
               T := Transform_Array_Negation
                 (Right      => Right,
                  Right_Type => Right_Type,
                  Domain     => Domain,
                  Ada_Node   => Ada_Node,
                  Do_Check   => Domain = EW_Prog);
            else
               if Domain = EW_Term then
                     T :=
                       New_Call
                         (Ada_Node => Ada_Node,
                       Domain   => Domain,
                       Name     => M_Boolean.Notb,
                       Args     =>
                         (1 => Insert_Simple_Conversion
                            (Ada_Node => Ada_Node,
                             Domain   => Domain,
                             Expr     => Right,
                             To       => EW_Bool_Type)),
                       Typ      => EW_Bool_Type);
               else
                  T :=
                    New_Not
                      (Right  => Insert_Simple_Conversion
                         (Ada_Node => Ada_Node,
                          Domain   => Domain,
                          Expr     => Right,
                          To       => EW_Bool_Type),
                       Domain => Domain);
               end if;
            end if;

         when N_Op_And | N_Op_Or | N_Op_Xor =>
            if Is_Array_Type (Left_Type) then
               T := Transform_Array_Logical_Op
                 (Op        => Op,
                  Left      => Left,
                  Right     => Right,
                  Left_Type => Left_Type,
                  Domain    => Domain,
                  Ada_Node  => Ada_Node,
                  Do_Check  => Domain = EW_Prog);
            else
               declare
                  Base  : constant W_Type_Id :=
                    (if Is_Boolean_Type (Return_Type) then EW_Bool_Type
                     else Base_Why_Type (Return_Type));
                  L_Why : constant W_Expr_Id :=  Insert_Simple_Conversion
                    (Ada_Node => Ada_Node,
                     Domain   => Domain,
                     Expr     => Left,
                     To       => Base);
                  R_Why : constant W_Expr_Id :=  Insert_Simple_Conversion
                    (Ada_Node => Ada_Node,
                     Domain   => Domain,
                     Expr     => Right,
                     To       => Base);
               begin
                  if Op = N_Op_And then
                     T := New_And_Expr (L_Why, R_Why, Domain, Base);
                  else
                     if Op = N_Op_Or then
                        T := New_Or_Expr (L_Why, R_Why, Domain, Base);
                     else
                        T := New_Xor_Expr (L_Why, R_Why, Domain, Base);
                     end if;

                     --  If we're dealing with modulars of non binary modulus
                     --  or and xor might overflow : we need to take the
                     --  modulo of the result.

                     if Is_Modular_Integer_Type (Return_Type) and then
                       Non_Binary_Modulus (Return_Type)
                     then
                        T := Apply_Modulus_Or_Rounding
                          (Op     => Op,
                           E      => Return_Type,
                           T      => T,
                           Domain => Domain);
                     end if;
                  end if;
               end;
            end if;

         when N_Op_Concat =>

            T := Transform_Concatenation
              (Left               => Left,
               Right              => Right,
               Left_Type          => Left_Type,
               Right_Type         => Right_Type,
               Return_Type        => Return_Type,
               Is_Component_Left  => not Covers (Left_Type, Return_Type),
               Is_Component_Right => not Covers (Right_Type, Return_Type),
               Domain             => Domain,
               Ada_Node           => Ada_Node);

         when N_Op_Shift =>
            Ada.Text_IO.Put_Line ("[New_Op_Expr] kind ="
                                  & Node_Kind'Image (Op));
            raise Not_Implemented;
      end case;
      return T;
   end New_Op_Expr;

   ------------------------
   -- New_Predicate_Call --
   ------------------------

   function New_Predicate_Call
     (Ty     : Entity_Id;
      W_Expr : W_Term_Id;
      Params : Transformation_Params) return W_Pred_Id
   is
      Variables : Flow_Id_Sets.Set;

   begin
      Variables_In_Dynamic_Invariant (Ty, Variables);

      declare
         Vars  : constant W_Expr_Array :=
           Get_Args_From_Variables
             (To_Name_Set (Variables), Params.Ref_Allowed);
         Num_B : constant Positive := 1 + Vars'Length;
         Args  : W_Expr_Array (1 .. Num_B);

      begin
         Args (1)          := +W_Expr;
         Args (2 .. Num_B) := Vars;

         return +New_Call (Name => E_Symb (Ty, WNE_Dynamic_Predicate),
                           Args => Args,
                           Typ  => EW_Bool_Type);
      end;
   end New_Predicate_Call;

   -------------------------
   -- New_Predicate_Check --
   -------------------------

   function New_Predicate_Check
     (Ada_Node : Node_Id;
      Ty       : Entity_Id;
      W_Expr   : W_Expr_Id) return W_Prog_Id
   is
      Check : constant W_Pred_Id :=
        Compute_Dynamic_Predicate (Expr    => +W_Expr,
                                   Ty      => Ty,
                                   Params  => Body_Params);
   begin
      return New_Assert
        (Pred =>
           New_Label (Labels => New_VC_Labels (Ada_Node, VC_Predicate_Check),
                      Def    => +Check),
         Assert_Kind => EW_Assert);
   end New_Predicate_Check;

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
               Ty      : constant Entity_Id := Etype (Prefix (N));

               --  For private types, functions are declared in the first
               --  ancestor only

               Rec_Ty  : constant Entity_Id := Retysp (Ty);
               R_Expr  : constant W_Expr_Id :=
                 Insert_Simple_Conversion (Ada_Node => N,
                                           Domain   => EW_Term,
                                           Expr     => Expr,
                                           To       => Type_Of_Node (Rec_Ty));
            begin
               return
                 New_Ada_Record_Access
                   (Ada_Node => N,
                    Domain   => Domain,
                    Name     => R_Expr,
                    Ty       => Rec_Ty,
                    Field    => Sel_Ent);
            end;

         when N_Indexed_Component =>

            --  ??? Save the index in a temporary variable

            declare
               Ar      : constant Node_Id := Prefix (N);
               Ar_Tmp  : constant W_Expr_Id := New_Temp_For_Expr (Expr);
               Dim     : constant Pos := Number_Dimensions (Type_Of_Node (Ar));
               Indices : W_Expr_Array (1 .. Integer (Dim));
               Cursor  : Node_Id := First (Expressions (N));
               Count   : Positive := 1;
            begin
               while Present (Cursor) loop
                  Indices (Count) :=
                     Transform_Expr
                      (Cursor,
                       Base_Why_Type_No_Bool (Node_Id'(Type_Of_Node (Cursor))),
                       Domain,
                       Params);

                  --  Insert Index Check if needed

                  if Domain = EW_Prog and then Do_Range_Check (Cursor) then
                     Indices (Count) := +Do_Index_Check
                       (Ada_Node => Cursor,
                        Arr_Expr => Ar_Tmp,
                        W_Expr   => Indices (Count),
                        Dim      => Count);
                  end if;

                  Count := Count + 1;
                  Next (Cursor);
               end loop;

               return
                 +Binding_For_Temp (Domain => EW_Prog,
                                    Tmp    => Ar_Tmp,
                                    Context => New_Array_Access
                                      (Ada_Node  => N,
                                       Domain    => Domain,
                                       Ar        => Ar_Tmp,
                                       Index     => Indices));
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
      Params      : Transformation_Params) return W_Expr_Id
   is
      Result : W_Expr_Id;
   begin
      case Nkind (N) is
         when N_Selected_Component | N_Identifier =>

            --  In fact identifiers can refer to components in the case of
            --  protected objects. But this is the only case, and we assert
            --  this here.

            pragma Assert
              (if Nkind (N) = N_Identifier
               then Is_Protected_Component_Or_Discr_Or_Part_Of (Entity (N)));

            --  The code should never update a discrimiant by assigning to it.

            declare
               Selector : constant Entity_Id :=
                 (if Nkind (N) = N_Identifier then Entity (N)
                  else Entity (Selector_Name (N)));
            begin
               pragma Assert (Ekind (Selector) /= E_Discriminant);

               Result := New_Ada_Record_Update
                 (Ada_Node => N,
                  Domain   => Domain,
                  Name     => Pref,
                  Field    => Selector,
                  Value    =>
                    Insert_Simple_Conversion
                      (Ada_Node => N,
                       Domain   => Domain,
                       Expr     => Value,
                       To       =>
                         EW_Abstract (Etype (Selector))));
            end;

         when N_Indexed_Component =>
            declare
               Dim     : constant Pos :=
                  Number_Dimensions (Type_Of_Node (Prefix (N)));
               Ar_Tmp  : constant W_Expr_Id := New_Temp_For_Expr (Pref);
               Indices : W_Expr_Array (1 .. Integer (Dim));
               Cursor  : Node_Id := First (Expressions (N));
               Count   : Positive := 1;
            begin
               while Present (Cursor) loop
                  Indices (Count) :=
                     Transform_Expr
                      (Cursor,
                       Base_Why_Type_No_Bool
                         (Entity_Id'(Type_Of_Node (Cursor))),
                       EW_Prog,
                       Params);

                  --  Insert Index Check if needed

                  if Domain = EW_Prog and then Do_Range_Check (Cursor) then
                     Indices (Count) := +Do_Index_Check
                       (Ada_Node => Cursor,
                        Arr_Expr => Ar_Tmp,
                        W_Expr   => Indices (Count),
                        Dim      => Count);
                  end if;

                  Count := Count + 1;
                  Next (Cursor);
               end loop;
               Result := +Binding_For_Temp
                 (Domain => EW_Prog,
                  Tmp    => Ar_Tmp,
                  Context => New_Array_Update
                    (Ada_Node  => N,
                     Ar        => Pref,
                     Index     => Indices,
                     Value     =>
                       Insert_Simple_Conversion
                         (Ada_Node => N,
                          Domain   => Domain,
                          Expr     => Value,
                          To       =>
                            EW_Abstract (Component_Type
                              (Type_Of_Node (Prefix (N))))),
                     Domain    => Domain));
            end;

         when N_Slice =>
            declare
               Prefix_Expr : constant W_Expr_Id :=
                 +Transform_Expr
                 (Prefix (N),
                  Domain        => EW_Term,
                  Expected_Type => Get_Type (Pref),
                  Params        => Params);
               Prefix_Name : constant W_Expr_Id :=
                 New_Temp_For_Expr (Prefix_Expr, True);
               Value_Name  : constant W_Expr_Id :=
                 New_Temp_For_Expr (Value, True);
               Dim     : constant Pos :=
                  Number_Dimensions (Type_Of_Node (Prefix (N)));
               Result_Id   : constant W_Identifier_Id :=
                 New_Result_Ident (Get_Type (Pref));
               Binders     : constant W_Identifier_Array :=
                 New_Temp_Identifiers (Positive (Dim), Typ => EW_Int_Type);
               Indexes     : constant W_Expr_Array := To_Exprs (Binders);
               Range_Pred  : constant W_Expr_Id :=
                               Transform_Discrete_Choice
                                 (Choice => Discrete_Range (N),
                                  Choice_Type => Empty,
                                  Expr   => Indexes (1),
                                  Domain => EW_Pred,
                                  Params => Params);
               In_Slice_Eq : constant W_Pred_Id :=
                               New_Element_Equality
                                 (Left_Arr   => +Result_Id,
                                  Right_Arr  => Value_Name,
                                  Index      => Indexes);
               Unchanged   : constant W_Pred_Id :=
                               New_Element_Equality
                                 (Left_Arr   => +Result_Id,
                                  Right_Arr  => Prefix_Name,
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

               --  If the prefix is not in split form, then its bounds are
               --  contained in the object. We should assume that they are
               --  preserved by the assignment.

               Bounds      : constant W_Pred_Id :=
                 (if Type_Get_Type_Kind (+Get_Type (Pref)) = EW_Abstract
                  then New_Bounds_Equality (Left_Arr  => Prefix_Name,
                                            Right_Arr => +Result_Id,
                                            Dim       => Positive (Dim))
                  else True_Pred);
            begin
               Result :=
                 +New_Simpl_Any_Prog (T    => Get_Type (Pref),
                                      Pred =>
                                        +New_And_Then_Expr
                                          (Left   => +Bounds,
                                           Right  => Quantif,
                                           Domain => EW_Pred));
               Result := Binding_For_Temp (Domain  => EW_Prog,
                                           Tmp     => Value_Name,
                                           Context => Result);
               Result := Binding_For_Temp (Domain  => EW_Prog,
                                           Tmp     => Prefix_Name,
                                           Context => Result);
            end;

         when others =>
            Ada.Text_IO.Put_Line ("[One_Level_Update] kind ="
                                  & Node_Kind'Image (Nkind (N)));
            raise Not_Implemented;
      end case;

      --  If the target type has a direct or inherited predicate, generate a
      --  corresponding check.

      declare
         Ty : constant Entity_Id := Get_Ada_Node (+Get_Type (Pref));
      begin
         if Domain = EW_Prog
           and then Present (Ty)
           and then Has_Predicates (Ty)
         then
            Result := +Insert_Predicate_Check
              (Ada_Node => N,
               Check_Ty => Ty,
               W_Expr   => +Result,
               Var_Ent  => Get_Ada_Node (+Pref));
         end if;
      end;

      return Result;
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
           Expr      => Insert_Simple_Conversion (Domain   => Subdomain,
                                                  Expr     => T,
                                                  To       => Base_Type));

      --  In programs, we generate a check that the range_constraint of a
      --  subtype_indication is compatible with the given subtype.

      if Domain = EW_Prog
        and then Nkind (N) = N_Subtype_Indication
      then
         R := +Sequence
           (Check_Subtype_Indication (Params   => Params,
                                      N        => N,
                                      Sub_Type => Etype (N)),
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
                          Type_Of_Node (Etype (E)),
                          Subdomain,
                          Params),
                       Context => T);
               end;

            when N_Null_Statement
               | N_Freeze_Entity =>
               null;

            when N_Pragma =>
               if Is_Ignored_Pragma_Check (N) then
                  null;
               else
                  raise Program_Error;
               end if;

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
                    Typ  => Type_Of_Node (Etype (Defining_Identifier (N))));

               Insert_Entity
                 (Defining_Identifier (N),
                  Id);

            when N_Null_Statement
               | N_Freeze_Entity =>
               null;

            when N_Pragma =>
               if Is_Ignored_Pragma_Check (N) then
                  null;
               else
                  raise Program_Error;
               end if;

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
         Values       : out Node_Lists.List;
         Types        : out Node_Lists.List;
         Index_Values : out Node_Lists.List;
         Index_Types  : out Node_Lists.List);
      --  Extract parts of the aggregate Expr that will be passed in
      --  parameter to the logic function for the aggregate.
      --  Collect these parameters in Values, with the corresponding type
      --  stored at the same position in Types.
      --  For a normal aggregate each element of Values is an element of the
      --  (possibly multi-dimensional) aggregate.
      --  For a 'Update aggregate, the choice indexes are
      --  collected in Values in addition to the elements.
      --  For a normal aggregate, each element of Index_Values is a
      --  component_association whose choices need to be checked against
      --  the type at the same position in Base_Types.

      procedure Generate_Logic_Function
        (Expr   : Node_Id;
         Values : Node_Lists.List;
         Types  : Node_Lists.List);
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
         Values       : Node_Lists.List;
         Types        : Node_Lists.List;
         Index_Values : Node_Lists.List;
         Index_Types  : Node_Lists.List) return W_Expr_Id;
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
         Values       : Node_Lists.List;
         Types        : Node_Lists.List;
         Index_Values : Node_Lists.List;
         Index_Types  : Node_Lists.List) return W_Expr_Id
      is
         use Node_Lists;

         Cnt      : Positive;
         Value    : Node_Lists.Cursor;
         Typ      : Node_Lists.Cursor;
         Args     : W_Expr_Array (1 .. Integer (Values.Length));
         R        : W_Expr_Id;

      begin
         --  Compute the arguments for the function call

         Cnt   := 1;
         Value := Values.First;
         Typ   := Types.First;
         while Value /= No_Element loop
            Args (Cnt) :=
              Transform_Expr
                (Element (Value),
                 Type_Of_Node (Element (Typ)),
                 Domain,
                 Params);

            --  Attributes of record array elements have default values

            if Has_Record_Type (Element (Typ))
              or else Full_View_Not_In_SPARK (Element (Typ))
            then
               Args (Cnt) := New_Record_Attributes_Update
                 (Domain   => Domain,
                  Name     => Args (Cnt),
                  Ty       => Element (Typ));
            end if;
            Next (Value);
            Next (Typ);
            Cnt := Cnt + 1;
         end loop;

         --  Compute the call

         R := New_Call (Ada_Node => Expr,
                        Domain   => Domain,
                        Name     => Func,
                        Args     => Args,
                        Typ      => Type_Of_Node (Etype (Expr)));

         --  Special case for choices of normal aggregate:
         --  In programs, we generate a check that all the choices are
         --  compatible with their index subtype:
         --  . a non-static value of choice must belong to the index subtype
         --  . the range_constraint of a subtype_indication must be compatible
         --    with the given subtype.
         --  Note that checks are done with respect to the aggregate's type
         --  Etype, as the aggregate's Etype may not respect its parent's
         --  constraints.
         --  For 'Update aggregates, choices are passed as parameters and
         --  checks inserted in Transform_Expr when arguments for the
         --  function call are computed, above.

         if not In_Attribute_Update and then Domain = EW_Prog then
            Value    := Index_Values.First;
            Typ      := Index_Types.First;

            while Value /= No_Element loop
               R := +Sequence
                 (New_Ignore
                    (Prog =>
                         +Transform_Discrete_Choices
                       (Choices      => Choices (Element (Value)),
                        Choice_Type  => Element (Typ),
                        Matched_Expr =>  --  The value does not matter here
                          New_Discrete_Constant
                            (Value => Uint_0,
                             Typ =>
                               Base_Why_Type_No_Bool (Element (Typ))),
                        Cond_Domain  => EW_Prog,
                        Params       => Params)),
                  +R);
               Next (Value);
               Next (Typ);
            end loop;
         end if;

         --  if the aggregate has known bounds, we use this information if it
         --  is not contained in the type

         if Domain = EW_Prog
           and then Present (Aggregate_Bounds (Expr))
           and then not Is_Static_Array_Type (Etype (Expr))
         then
            declare
               Temp : constant W_Expr_Id := New_Temp_For_Expr (R, True);
               A1, A2 : W_Prog_Id;
               Typ : constant Node_Id := First_Index (Etype (Etype (Expr)));
               W_Typ : constant W_Type_Id :=
                 (if Typ = Empty then EW_Int_Type else
                     Base_Why_Type_No_Bool (Typ));
            begin
               A1 :=
                 New_Assume_Statement
                   (Pred =>
                      New_Call
                        (Name => Why_Eq,
                         Typ  => EW_Bool_Type,
                         Args =>
                           (1 =>
                            Get_Array_Attr (EW_Term, Temp, Attribute_First, 1),
                            2 =>
                              Transform_Expr
                                (Low_Bound (Aggregate_Bounds (Expr)),
                                 W_Typ,
                                 EW_Term,
                                 Params))));
               A2 :=
                 New_Assume_Statement
                   (Pred =>
                      New_Call
                        (Name => Why_Eq,
                         Typ  => EW_Bool_Type,
                         Args =>
                           (1 =>
                             Get_Array_Attr (EW_Term, Temp, Attribute_Last, 1),
                            2 =>
                              Transform_Expr
                                (High_Bound (Aggregate_Bounds (Expr)),
                                 W_Typ,
                                 EW_Term,
                                 Params))));
               R := +Sequence (A2, +Temp);
               R := +Sequence (A1, +R);
               R := Binding_For_Temp (Expr, EW_Prog, Temp, R);
            end;
         end if;

         --  Possibly check the predicate on the aggregate

         if Domain = EW_Prog
           and then Has_Predicates (Etype (Expr))
         then
            R := +Insert_Predicate_Check (Ada_Node => Expr,
                                          Check_Ty => Etype (Expr),
                                          W_Expr   => +R);
         end if;

         return R;
      end Complete_Translation;

      -----------------------------
      -- Generate_Logic_Function --
      -----------------------------

      procedure Generate_Logic_Function
        (Expr   : Node_Id;
         Values : Node_Lists.List;
         Types  : Node_Lists.List)
      is
         use Node_Lists;

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
                            Gen_Marker   => False,
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
         Value         : Node_Lists.Cursor;
         Typ           : Node_Lists.Cursor;

         --  Variables for the call, guard and proposition for the axiom

         Aggr          : W_Expr_Id;
         Def_Pred      : W_Pred_Id;

         Aggr_Temp     : constant W_Identifier_Id :=
           New_Temp_Identifier (Typ => Ret_Type);

         --  Select file for the declarations

         Decl_File     : Why_Section renames
           Why_Sections (Dispatch_Entity (Expr));

      --  Start of processing for Generate_Logic_Function

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
                 New_Temp_Identifier (Typ => Type_Of_Node (Element (Typ)));
               B     : constant Binder_Type :=
                 (Ada_Node => Empty,
                  B_Name   => Ident,
                  B_Ent    => Null_Entity_Name,
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
                     Typ      => Type_Of_Node (Etype (Expr)));

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
           (Decl_File, E_Module (Expr),
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
         Values       : out Node_Lists.List;
         Types        : out Node_Lists.List;
         Index_Values : out Node_Lists.List;
         Index_Types  : out Node_Lists.List)
      is
         Typ     : constant Entity_Id := Type_Of_Node (Etype (Etype (Expr)));
         --  We should use the aggregate's type Etype here for the checks as
         --  the aggregate's type may have incorrect index bounds.
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
            Index               : Node_Id;  --  Index type
            Expr_Or_Association : Node_Id)
         is
            Expr   : Node_Id;
            Choice : Node_Id;
            Rng    : Node_Id;

         begin
            --  If Expr_Or_Association is a component association, first we
            --  go through the component association and collect the
            --  choices to be used later for:
            --  * Index checks, in the case of normal aggregates.
            --  * Parameters to the logic function, in the case of 'Update
            --  aggregates.

            if Nkind (Expr_Or_Association) = N_Component_Association
              and then not Is_Others_Choice (Choices (Expr_Or_Association))
            then
               Index_Values.Append (Expr_Or_Association);
               Index_Types.Append (Etype (Index));

               --  For 'Update aggregates we also need the choices as
               --  parameters since they can be dynamic

               if In_Attribute_Update then

                  --  Collect the choices as parameters.
                  --  We cannot use Index_Values directly since they store
                  --  the whole associations. Instead, populate Values with
                  --  the parameters needed.

                  Choice := First (Choices (Expr_Or_Association));
                  while Present (Choice) loop
                     case Nkind (Choice) is
                        when N_Range =>

                           --  The high and low bounds of a range both
                           --  need to be parameters.

                           Rng := Get_Range (Choice);
                           Values.Append (Low_Bound (Rng));
                           Types.Append (Etype (Index));
                           Values.Append (High_Bound (Rng));
                           Types.Append (Etype (Index));

                        when N_Aggregate =>

                           --  This is a special choice, the LHS of an
                           --  association of a 'Update of a
                           --  multi-dimensional array,
                           --  for example: (I, J, K) of
                           --  'Update((I, J, K) => New_Val)

                           pragma Assert
                             (Dim < Num_Dim and then Dim = 1
                                and then No (Component_Associations (Choice)));
                           declare
                              Multi_Exprs : constant List_Id :=
                                Expressions (Choice);
                              Multi_Expression : Node_Id :=
                                Nlists.First (Multi_Exprs);

                              Current_Index : Node_Id := Index;
                              --  Dim = 1 so Index is still first index here

                           begin
                              pragma Assert (List_Length (Multi_Exprs) =
                                               Num_Dim);

                              while Present (Multi_Expression) loop
                                 Values.Append (Multi_Expression);
                                 Types.Append (Etype (Current_Index));
                                 Next (Multi_Expression);
                                 Next_Index (Current_Index);
                              end loop;
                              pragma Assert (No (Current_Index));
                           end;

                        when others =>
                           Values.Append (Choice);
                           Types.Append (Etype (Index));
                     end case;
                     Next (Choice);
                  end loop;
               end if;
            end if;

            --  Next, for both positional and named associations, and for
            --  both normal and for 'Update aggregates, we fill the
            --  component expressions to the arrays Values and Types, to
            --  later be used as parameters.

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

               if Dim < Num_Dim and then not In_Attribute_Update then

                  --  Normal, multidimensional aggregate, for example:
                  --  Array_2D'(1      => (2 => Expr_1, others => Expr_2),
                  --            others => (others => Expr_3))
                  --
                  --  The components are aggregates as long as Dim < Num_Dim.
                  --  Keep recursively peeling the aggregates off.

                  pragma Assert (Nkind (Expr) = N_Aggregate);
                  Traverse_Rec_Aggregate (Dim + 1, Next_Index (Index), Expr);
               else

                  --  Two cases here:
                  --
                  --  1) A single dimensional aggregate, normal or 'Update,
                  --  (for example an innermost of a multidimensional
                  --  aggregate), or
                  --
                  --  2) A multidimensional 'Update aggregate of the form
                  --  'Update((I, J, K) => New_Val)
                  --
                  --  in both cases there are no more aggregates to peel off.

                  pragma Assert (Dim = Num_Dim or else
                                   (In_Attribute_Update and then Dim = 1));
                  declare
                     Exp_Type  : constant Node_Id := Component_Type (Typ);
                  begin

                     --  Collecting component expression for later use as
                     --  parameter.

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

            --  Positional association is not allowed in 'Update aggregate
            --  (except in an inner aggregate that is the choice in a
            --  component association of a multidimensional 'Update
            --  aggregate, but never on the outer level we are at here).

            pragma Assert (if Present (Expression) then
                             not In_Attribute_Update);

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

      --  Start of processing for Get_Aggregate_Elements

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
         Binders : Binder_Array (1 .. Positive (Num_Dim));

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

               if Dim < Num_Dim and then not In_Attribute_Update then
                  pragma Assert (Nkind (Expr) = N_Aggregate);
                  return Callback (Dim + 1, Expr);
               else

                  --  For single dimensional aggregates (normal or
                  --  'Update), and for multidimensional 'Update aggregates
                  --  there will be no more nested aggregates, so no
                  --  recursive callback, go ahead and create array
                  --  access and comparison.

                  declare
                     Binder  : constant Item_Type :=
                       Ada_Ent_To_Why.Element (Args, Expr);
                     Arg_Val : constant W_Expr_Id :=
                       (case Binder.Kind is
                           when Regular => +Binder.Main.B_Name,
                           when UCArray => +Binder.Content.B_Name,
                           when others  => raise Program_Error);
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
                        Value := Insert_Simple_Conversion
                          (Domain => EW_Term,
                           Expr   => Arg_Val,
                           To     => EW_Abstract (Component_Type (Typ)));
                     end if;

                     Read := New_Array_Access (Ada_Node => Expr_Or_Association,
                                               Domain   => EW_Term,
                                               Ar       => Arr,
                                               Index    => Indexes);
                     return New_Comparison (Symbol => Why_Eq,
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
            Typ        : constant W_Type_Id := Base_Why_Type_No_Bool
              (Etype (Rng));
            Low        : constant Node_Id := Low_Bound (Rng);
            First, Val : W_Expr_Id;

         begin

            if Is_Static_Expression (Low) then
               Val :=
                 New_Discrete_Constant
                   (Value => Expr_Value (Low) + UI_From_Int (Offset),
                    Typ   => Typ);
            else
               First := New_Attribute_Expr (Etype (Rng),
                                            EW_Term,
                                            Attribute_First,
                                            Params);

               Val :=
                 New_Discrete_Add (Domain => Domain,
                                   Left   => First,
                                   Right  => New_Discrete_Constant
                                     (Value => UI_From_Int (Offset),
                                      Typ   => Typ));
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
            Arg_Choice : W_Expr_Id;
         begin
            while Present (Choice) loop
               if In_Attribute_Update then
                  case Nkind (Choice) is
                     when N_Range =>
                        declare
                           Low  : constant Node_Id :=
                             Low_Bound (Get_Range (Choice));
                           High : constant Node_Id :=
                             High_Bound (Get_Range (Choice));
                           Arg_Low  : W_Expr_Id;
                           Arg_High : W_Expr_Id;
                        begin
                           Arg_Low :=
                             +Ada_Ent_To_Why.Element (Args, Low).Main.B_Name;
                           Arg_Low :=
                             Insert_Simple_Conversion (Domain => EW_Term,
                                                       Expr   => Arg_Low,
                                                       To     =>
                                                         Base_Why_Type_No_Bool
                                                         (Arg_Low));

                           Arg_High :=
                             +Ada_Ent_To_Why.Element (Args, High).Main.B_Name;

                           Arg_High :=
                             Insert_Simple_Conversion (Domain => EW_Term,
                                                       Expr   => Arg_High,
                                                       To     =>
                                                         Base_Why_Type_No_Bool
                                                        (Arg_High));
                           Rng_Expr :=
                             New_Range_Expr (Domain => EW_Pred,
                                             Low    => Arg_Low,
                                             High   => Arg_High,
                                             Expr   => Indexes (Integer (Dim))
                                            );
                        end;
                     when N_Aggregate =>
                        pragma Assert (Dim < Num_Dim and then Dim = 1);

                        --  This is a choice of a multidimensional 'Update,
                        --  for example (I, J, K) of
                        --  'Update((I, J, K) => New_Val).
                        --  Create a conjunction of comparisons, one for
                        --  each dimension.

                        declare
                           Conjunct     : W_Expr_Id := +True_Pred;
                           Arg_Index    : W_Expr_Id;
                           Multi_Exprs : constant List_Id :=
                             Expressions (Choice);
                           Multi_Assocs : constant List_Id :=
                             Component_Associations (Choice);
                           Multi_Expression : Node_Id :=
                             Nlists.First (Multi_Exprs);

                           --  Start with first dimension, Dim = 1 always
                           --  here.

                           Current_Dim  : Positive := 1;
                        begin
                           pragma Assert (No (Multi_Assocs)
                              and then List_Length (Multi_Exprs) = Num_Dim);

                           while Present (Multi_Expression) loop
                              Arg_Index :=
                                +Ada_Ent_To_Why.Element
                                (Args, Multi_Expression).Main.B_Name;
                              Arg_Index :=
                                Insert_Simple_Conversion
                                (Domain => EW_Term,
                                 Expr   => Arg_Index,
                                 To     => Base_Why_Type_No_Bool
                                   (Get_Type (Arg_Index)));
                              Rng_Expr :=
                                New_Comparison
                                (Symbol => Why_Eq,
                                 Left   => Indexes (Integer (Current_Dim)),
                                 Right  => Arg_Index,
                                 Domain => EW_Pred);
                              Conjunct := New_And_Expr (Left   => Conjunct,
                                                        Right  => Rng_Expr,
                                                        Domain => EW_Pred);
                              Next (Multi_Expression);
                              Current_Dim := Current_Dim + 1;
                           end loop;
                           pragma Assert (Integer (Current_Dim - 1) =
                                            Integer (Num_Dim));
                           Rng_Expr := Conjunct;
                        end;
                     when others =>
                        Arg_Choice :=
                          +Ada_Ent_To_Why.Element (Args, Choice).Main.B_Name;
                        Arg_Choice :=
                          Insert_Simple_Conversion (Domain => EW_Term,
                                                    Expr   => Arg_Choice,
                                                    To     =>
                                                       Base_Why_Type_No_Bool
                                                      (Get_Type (Arg_Choice)));

                        Rng_Expr :=
                          New_Comparison (Symbol => Why_Eq,
                                          Left   => Indexes (Integer (Dim)),
                                          Right  => Arg_Choice,
                                          Domain => EW_Pred);
                  end case;
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
                            (Symbol    => Why_Eq,
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
                         (Symbol    => Why_Eq,
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
                                       Expected_Type => Base_Why_Type_No_Bool
                                       (Etype (First (Choices (Association)))),
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

      --  Start of processing for Transform_Array_Component_Associations

      begin
         --  Fill the array of index nodes

         Ind_Arr (1) := First_Index (Typ);
         for Dim in 2 .. Num_Dim loop
            Ind_Arr (Dim) := Next_Index (Ind_Arr (Dim - 1));
         end loop;

         --  Define index variables

         for J in 1 .. Integer (Num_Dim) loop
            Binders (J) :=
              (B_Name => New_Temp_Identifier
                 (Typ => Nth_Index_Rep_Type_No_Bool (E   => Typ,
                                                     Dim => J)),
               B_Ent  => Null_Entity_Name,
               others => <>);
            Indexes (J) := +Binders (J).B_Name;
         end loop;

         --  Create the proposition defining the aggregate

         if not In_Attribute_Update
           and then Is_Simple_Aggregate (Dim => 1, Expr => Expr)
         then
            return +Transform_Rec_Simple_Aggregate (Dim => 1, Expr => Expr);
         else
            return New_Universal_Quantif
              (Binders => Binders,
               Pred    =>
                 +Transform_Rec_Aggregate
                 (Dim => 1, Expr => Expr));
         end if;
      end Transform_Array_Component_Associations;

      --  Elements of the aggregate

      Values       : Node_Lists.List;
      Types        : Node_Lists.List;
      Index_Values : Node_Lists.List;
      Index_Types  : Node_Lists.List;

   --  Start of processing for Transform_Aggregate

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
     (Op        : N_Op_Compare;
      Left      : W_Expr_Id;
      Right     : W_Expr_Id;
      Domain    : EW_Domain;
      Ada_Node  : Node_Id) return W_Expr_Id
   is
      Subdomain : constant EW_Domain :=
        (if Domain = EW_Pred then EW_Term else Domain);
      Args      : W_Expr_Array (1 .. 6);
      T         : W_Expr_Id;
      Left_Expr : constant W_Expr_Id := New_Temp_For_Expr (Left);
      Right_Expr : constant W_Expr_Id := New_Temp_For_Expr (Right);
      Arg_Ind    : Positive := 1;
   begin
      Add_Array_Arg (Subdomain, Args, Left_Expr, Arg_Ind);
      Add_Array_Arg (Subdomain, Args, Right_Expr, Arg_Ind);
      T :=
        New_Call
          (Ada_Node => Ada_Node,
           Domain   => Subdomain,
           Name     => Get_Array_Theory_1_Comp (Get_Ada_Node (+Left)).Compare,
           Args     => Args,
           Typ      => EW_Int_Type);
      T := Binding_For_Temp (Domain  => Domain,
                             Tmp     => Left_Expr,
                             Context => T);
      T := Binding_For_Temp (Domain  => Domain,
                             Tmp     => Right_Expr,
                             Context => T);
      T := New_Comparison
        (Symbol    => Transform_Compare_Op (Op, EW_Int_Type, Domain),
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
     (Op        : N_Op_Compare;
      Left      : W_Expr_Id;
      Right     : W_Expr_Id;
      Left_Type : Entity_Id;
      Domain    : EW_Domain;
      Ada_Node  : Node_Id) return W_Expr_Id
   is
      Dim       : constant Positive :=
        Positive (Number_Dimensions (Left_Type));
      Subdomain : constant EW_Domain :=
        (if Domain = EW_Pred then EW_Term else Domain);
      Args      : W_Expr_Array (1 .. 4 * Dim + 2);
      T         : W_Expr_Id;
      Left_Expr : constant W_Expr_Id := New_Temp_For_Expr (Left);
      Right_Expr : constant W_Expr_Id := New_Temp_For_Expr (Right);
      Arg_Ind    : Positive := 1;
   begin
      Add_Array_Arg (Subdomain, Args, Left_Expr, Arg_Ind);
      Add_Array_Arg (Subdomain, Args, Right_Expr, Arg_Ind);
      T :=
        New_Call
          (Ada_Node => Ada_Node,
           Domain   => Subdomain,
           Name     =>
             Get_Array_Theory (Left_Opnd (Ada_Node)).Bool_Eq,
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
           (Symbol    => Transform_Compare_Op (Op, EW_Bool_Type, Domain),
            Left      => T,
            Right     => New_Literal (Domain => Subdomain,
                                      Value  => EW_True),
            Domain    => Domain);
      elsif Op = N_Op_Ne then
         T :=
           New_Call (Domain => Domain,
                     Name   => M_Boolean.Notb,
                     Args   => (1 => T),
                     Typ    => EW_Bool_Type);
      end if;
      return T;
   end Transform_Array_Equality;

   --------------------------------
   -- Transform_Array_Logical_Op --
   --------------------------------

   function Transform_Array_Logical_Op
     (Op        : N_Binary_Op;
      Left      : W_Expr_Id;
      Right     : W_Expr_Id;
      Left_Type : Entity_Id;
      Domain    : EW_Domain;
      Ada_Node  : Node_Id;
      Do_Check  : Boolean) return W_Expr_Id
   is
      Subdomain : constant EW_Domain :=
        (if Domain = EW_Pred then EW_Term else Domain);
      Args      : W_Expr_Array (1 .. 6);
      T         : W_Expr_Id;
      Arg_Ind   : Positive := 1;
      Left_Expr : constant W_Expr_Id := New_Temp_For_Expr (Left);
      Right_Expr : constant W_Expr_Id := New_Temp_For_Expr (Right);
      Array_Theory : constant M_Array_1_Bool_Op_Type :=
        Get_Array_Theory_1_Bool_Op (Left_Opnd (Ada_Node));
      W_Op      : constant W_Identifier_Id :=
        (case Op is
            when N_Op_And => Array_Theory.Andb,
            when N_Op_Or  => Array_Theory.Orb,
            when N_Op_Xor => Array_Theory.Xorb,
            when others => raise Program_Error);

      Left_Length  : constant W_Expr_Id :=
        Build_Length_Expr (Domain => EW_Term, Expr => Left_Expr, Dim => 1);
      Right_Length : constant W_Expr_Id :=
        Build_Length_Expr (Domain => EW_Term, Expr => Right_Expr, Dim => 1);
      Length_Check : constant W_Expr_Id :=
        New_Call
          (Domain => EW_Pred,
           Name   => Why_Eq,
           Typ    => EW_Bool_Type,
           Args   => (+Left_Length, +Right_Length));

      Index_Type : constant W_Type_Id :=
        (if First_Index (Left_Type) = Empty
         then EW_Int_Type
         else Base_Why_Type_No_Bool (First_Index (Left_Type)));

      --  if Length (Left) > 0 then not (Left'First = Left'Last and
      --                                 Left'Last  = 1);
      Range_Check  : constant W_Expr_Id :=
        New_Conditional
          (Domain    => EW_Pred,
           Condition =>
             New_Call
               (Domain => EW_Pred,
                Typ    => EW_Bool_Type,
                Name   => Int_Infix_Gt,
                Args   => (+Left_Length,
                           New_Integer_Constant (Value => Uint_0))),
           Then_Part =>
             New_Not
               (Domain   => EW_Pred,
                Right    =>
                  New_And_Expr
                    (Left   =>
                           New_Call
                       (Domain => EW_Pred,
                        Typ    => EW_Bool_Type,
                        Name   => Why_Eq,
                        Args   =>
                          (1 =>
                               +E_Symb (Component_Type (Left_Type),
                                        WNE_Attr_First),
                           2 =>
                               +E_Symb (Component_Type (Left_Type),
                                        WNE_Attr_Last))),
                     Right  =>
                       New_Call
                         (Domain => EW_Pred,
                          Name   => Why_Eq,
                          Typ    => EW_Bool_Type,
                          Args   =>
                            (1 => New_Discrete_Constant (Value => Uint_1,
                                                         Typ   => Index_Type),
                             2 =>
                               +E_Symb (Component_Type (Left_Type),
                                        WNE_Attr_Last))),
                     Domain => EW_Pred)));
   begin
      Add_Array_Arg (Subdomain, Args, Left_Expr, Arg_Ind);
      Add_Array_Arg (Subdomain, Args, Right_Expr, Arg_Ind);

      --  Call to operator

      T :=
        New_Call
          (Ada_Node => Ada_Node,
           Domain   => Subdomain,
           Name     => W_Op,
           Args     => Args);

      if Do_Check then

         --  Length check, Left and Right should have the same length

         T := +Sequence (New_Ignore (Prog =>
               New_Located_Assert (Ada_Node,
                                   +Length_Check,
                                   VC_Length_Check,
                                   EW_Assert)),
                         +T);

         --  Range check : for all I, Left (I) Op Right (I) should be in range.
         --  The only way to generate an element not in range using a binary
         --  operator is to call xor on arrays of the singleton subtype True of
         --  boolean.

         if not Is_Standard_Boolean_Type (Component_Type (Left_Type)) and then
           W_Op = Array_Theory.Xorb
         then
            T :=  +Sequence (New_Ignore (Prog =>
                     New_Located_Assert (Ada_Node,
                                         +Range_Check,
                                         VC_Range_Check,
                                         EW_Assert)),
                             +T);
         end if;
      end if;

      --  Conversion from base, first and right are attributes of left

      T := Array_Convert_From_Base
        (Domain => Subdomain,
         Target => Left_Type,
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
     (Right      : W_Expr_Id;
      Right_Type : Entity_Id;
      Domain     : EW_Domain;
      Ada_Node   : Node_Id;
      Do_Check   : Boolean) return W_Expr_Id
   is
      Subdomain : constant EW_Domain :=
        (if Domain = EW_Pred then EW_Term else Domain);
      Args      : W_Expr_Array (1 .. 3);
      T         : W_Expr_Id;
      Arg_Ind   : Positive := 1;
      Right_Expr : constant W_Expr_Id := New_Temp_For_Expr (Right);

      Right_Length : constant W_Expr_Id :=
        Build_Length_Expr (Domain => EW_Term, Expr => Right_Expr, Dim => 1);
      Range_Check  : constant W_Expr_Id :=
        New_Conditional
          (Domain    => EW_Pred,
           Condition =>
             New_Call
               (Domain => EW_Pred,
                Typ    => EW_Bool_Type,
                Name   => Int_Infix_Gt,
                Args   => (1 => +Right_Length,
                           2 => New_Integer_Constant (Value => Uint_0))),
           Then_Part =>
             New_Call
               (Domain => EW_Pred,
                Name   => Int_Infix_Lt,
                Typ    => EW_Bool_Type,
                Args   =>
                  (1 => +E_Symb (Component_Type (Right_Type), WNE_Attr_First),
                   2 =>
                     +E_Symb (Component_Type (Right_Type), WNE_Attr_Last))));
   begin
      Add_Array_Arg (Subdomain, Args, Right_Expr, Arg_Ind);

      --  Call to operator

      T :=
        New_Call
          (Ada_Node => Ada_Node,
           Domain   => Subdomain,
           Name     => Get_Array_Theory_1_Bool_Op (Ada_Node).Notb,
           Args     => Args);

      if Do_Check then

         --  Range check : for all I, Not Right (I) should be in range.
         --  The only way to generate an element not in range using negation
         --  is to call it on an array of a singleton subtype of boolean.

         if not Is_Standard_Boolean_Type (Component_Type (Right_Type)) then
            T :=  +Sequence (New_Ignore (Prog =>
                     New_Located_Assert (Ada_Node,
                                         +Range_Check,
                                         VC_Range_Check,
                                         EW_Assert)),
                             +T);
         end if;
      end if;

      --  Conversion from base

      T := Array_Convert_From_Base
        (Domain => Subdomain,
         Target => Right_Type,
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

   ------------------------------------
   -- Transform_Assignment_Statement --
   ------------------------------------

   function Transform_Assignment_Statement (Stmt : Node_Id) return W_Prog_Id
   is
      Lvalue     : constant Node_Id := Sinfo.Name (Stmt);
      Exp_Entity : constant W_Type_Id := Expected_Type_Of_Prefix (Lvalue);
      L_Type     : constant W_Type_Id := Type_Of_Node (Etype (Lvalue));
      T          : W_Prog_Id :=
        +Transform_Expr
        (Expression (Stmt),
         L_Type,
         EW_Prog,
         Params => Body_Params);
      Lgth_Check : constant Boolean :=
        Present (Get_Ada_Node (+L_Type)) and then

        --  Length check needed for assignment into a non-static array type

        (Is_Array_Type (Get_Ada_Node (+L_Type)) and then
           not Is_Static_Array_Type (Get_Ada_Node (+L_Type))); --   or else

         --  Discriminant check needed for assignment into a non-constrained
         --  record type. Constrained record type are handled by the
         --  conversion.

      Disc_Check : constant Boolean :=
        Present (Get_Ada_Node (+L_Type)) and then
        Has_Discriminants (Get_Ada_Node (+L_Type)) and then
        not Is_Constrained (Get_Ada_Node (+L_Type));
      Tmp      : constant W_Expr_Id :=
        New_Temp_For_Expr (+T, Lgth_Check or else Disc_Check);
   begin

      --  The Exp_Entity type is in fact the type that is expected in Why.
      --  The L_Type is a more precise type entity in Ada. We have to
      --  respect both constraints here, so we first convert to the Ada type
      --  (to get checks), and then convert to Why (without checks) to get the
      --  types right.

      if Lgth_Check then
         --           if Is_Array_Type (Get_Ada_Node (+L_Type)) then
         declare
            Check : W_Pred_Id := True_Pred;
            Lval  : constant W_Expr_Id :=
              New_Temp_For_Expr
                (Transform_Expr (Lvalue, EW_Pterm, Body_Params), True);
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
                       New_Call
                         (Domain => EW_Pred,
                          Name   => Why_Eq,
                          Typ    => EW_Bool_Type,
                          Args   => (+Input_Length, +Expected_Length)));
               end;
            end loop;
            T :=
              Sequence
                (New_Located_Assert
                   (Stmt, Check, VC_Length_Check, EW_Assert),
                 +Tmp);
            T := +Binding_For_Temp (Ada_Node => Empty,
                                    Domain   => EW_Prog,
                                    Tmp      => Lval,
                                    Context  => +T);
         end;
      elsif Disc_Check then

         --  Discriminants should be preserved by assignment except if the
         --  object is not constrained.

         declare
            Ty    : constant Entity_Id := Get_Ada_Node (+L_Type);
            Check : W_Expr_Id := +True_Pred;
            Lval  : constant W_Expr_Id :=
              New_Temp_For_Expr
                (Transform_Expr (Lvalue, EW_Pterm, Body_Params), True);
            Discr : Node_Id := First_Discriminant (Ty);
            D_Ty  : constant Entity_Id :=
              (if Full_View_Not_In_SPARK (Ty) then
                    Get_First_Ancestor_In_SPARK (Ty)
               else Ty);
         begin
            while Present (Discr) loop
               if not Is_Completely_Hidden (Discr) then
                  declare
                     Input_Discr    : constant W_Expr_Id :=
                       New_Ada_Record_Access
                         (Empty, EW_Term, Tmp, Discr, D_Ty);
                     Expected_Discr : constant W_Expr_Id :=
                       New_Ada_Record_Access
                         (Empty, EW_Term, Lval, Discr, D_Ty);
                  begin
                     Check :=
                       New_And_Then_Expr
                         (Domain => EW_Pred,
                          Left   => Check,
                          Right  =>
                            New_Call
                              (Domain => EW_Pred,
                               Name   => Why_Eq,
                               Typ    => EW_Bool_Type,
                               Args   => (+Input_Discr, +Expected_Discr)));
                  end;
               end if;
               Next_Discriminant (Discr);
            end loop;

            if Has_Defaulted_Discriminants (Ty) then
               Check := New_Conditional
                 (Domain      => EW_Pred,
                  Condition   =>
                    New_Is_Constrained_Access (Empty, EW_Term, Lval, Ty),
                  Then_Part   => Check);
            end if;

            T :=
              Sequence
                (New_Located_Assert
                   (Stmt, +Check, VC_Discriminant_Check, EW_Assert),
                 +Tmp);
            T := +Binding_For_Temp (Ada_Node => Empty,
                                    Domain   => EW_Prog,
                                    Tmp      => Lval,
                                    Context  => +T);
         end;
      elsif Is_Class_Wide_Type (Etype (Lvalue)) and then
        not Sem_Disp.Is_Tag_Indeterminate (Expression (Stmt))
      then
         declare
            Lval  : constant W_Expr_Id :=
              New_Temp_For_Expr
                (Transform_Expr (Lvalue, EW_Pterm, Body_Params), True);
            Pred : constant W_Pred_Id :=
              New_Call
                (Name => Why_Eq,
                 Typ  => EW_Bool_Type,
                 Args =>
                   (1 =>
                          New_Tag_Access
                      (Name => Lval, Domain => EW_Term,
                       Ty   => Etype (Lvalue)),
                    2 =>
                      New_Tag_Access
                        (Name => Tmp, Domain => EW_Term,
                         Ty   => Get_Ada_Node (+Get_Type (Tmp)))));
         begin
            T :=
              Sequence
                (New_Located_Assert
                   (Stmt, +Pred, VC_Tag_Check, EW_Assert),
                 +Tmp);
            T := +Binding_For_Temp (Ada_Node => Empty,
                                    Domain   => EW_Prog,
                                    Tmp      => Lval,
                                    Context  => +T);
         end;
      end if;
      T :=
        +Insert_Simple_Conversion
        (Domain => EW_Pterm,
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

      --  Do not generate old when references are not allowed.

      if not Params.Ref_Allowed then
         return Transform_Expr (Expr, Domain, Params);
      end if;

      --  Expressions that cannot be translated to predicates directly are
      --  translated to (boolean) terms, and compared to "True"

      if Domain = EW_Pred then
         return
           New_Call
             (Ada_Node => Expr,
              Domain   => EW_Pred,
              Typ      => EW_Bool_Type,
              Name     => Why_Eq,
              Args     =>
                (1 => +Transform_Attribute_Old (Expr, EW_Term, Params),
                 2 => +True_Term));
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
               T := +Name_For_Result;
            end if;

         when Attribute_Old =>
            T := Transform_Attribute_Old (Var, Domain, Params);

         when Attribute_Pred | Attribute_Succ =>

            --  'Succ and 'Pred on floating-point types are modelled as calls
            --  to logic functions next_representable and prev_representable
            --  for the corresponding type. The value of these functions should
            --  only be specified for values of the argument that do not lead
            --  to an overflow, so that a possible overflow check failure
            --  may be detected when computing Float'Succ(Float'Last) or
            --  Float'Pred(Float'First).

            if Is_Floating_Point_Type (Etype (Var)) then
               declare
                  Oper : constant W_Identifier_Id :=
                    (if Attr_Id = Attribute_Pred then
                        E_Symb (Etype (Var), WNE_Float_Pred)
                     else
                       E_Symb (Etype (Var), WNE_Float_Succ));
                  Arg : constant W_Expr_Id :=
                    Transform_Expr (First (Expressions (Expr)),
                                    EW_Real_Type,
                                    Domain,
                                    Params);
               begin
                  T := New_Call (Ada_Node => Expr,
                                 Domain   => Domain,
                                 Name     => Oper,
                                 Args     => (1 => Arg),
                                 Typ      => EW_Real_Type);
               end;

            --  For all discrete and fixed-point types, 'Succ is modelled as
            --  adding 1 to the representation value, and 'Pred is modelled
            --  as subtracting 1 to the representation value.

            elsif Is_Modular_Integer_Type (Etype (Var)) then
               declare
                  W_Type : constant W_Type_Id := Base_Why_Type (Etype (Var));
                  Op     : constant N_Op :=
                    (if Attr_Id = Attribute_Succ then
                        N_Op_Add
                     else
                        N_Op_Subtract);
                  Old    : W_Expr_Id;
                  Offset : constant W_Expr_Id :=
                    New_Modular_Constant (Typ => W_Type,
                                          Value => Uint_1);
                  NType : constant Node_Id := Etype (Expr);
               begin
                  Old := Transform_Expr (First (Expressions (Expr)),
                                         W_Type,
                                         Domain,
                                         Params);

                  T := New_Op_Expr (Op          => Op,
                                    Left        => Old,
                                    Right       => Offset,
                                    Left_Type   => NType,
                                    Right_Type  => NType,
                                    Return_Type => NType,
                                    Domain      => Domain,
                                    Ada_Node    => Expr);
               end;
            else
               declare
                  Op     : constant W_Identifier_Id :=
                    (if Attr_Id = Attribute_Succ then Int_Infix_Add
                     else Int_Infix_Subtr);
                  Old    : W_Expr_Id;
                  Offset : W_Expr_Id;
                  A_Type : constant Entity_Id := Etype (Var);
                  W_Type : W_Type_Id;
               begin
                  if Is_Discrete_Type (Etype (Var)) then
                     if Is_Standard_Boolean_Type (A_Type) then
                        W_Type := EW_Bool_Type;
                        Ada.Text_IO.Put_Line
                          ("[Transform_Attr] boolean"
                           & Attribute_Id'Image (Attr_Id));
                        raise Not_Implemented;
                     else
                        W_Type := EW_Int_Type;
                        Offset := New_Integer_Constant (Value => Uint_1);
                     end if;

                  else
                     pragma Assert (Is_Fixed_Point_Type (Etype (Var)));
                     W_Type := EW_Fixed_Type;
                     Offset := New_Fixed_Constant (Value => Uint_1);
                  end if;

                  Old := Transform_Expr (First (Expressions (Expr)),
                                         W_Type,
                                         Domain,
                                         Params);

                  T :=
                    New_Call
                      (Ada_Node => Expr,
                       Domain   => Domain,
                       Name     => Op,
                       Args     => (1 => Old, 2 => Offset),
                       Typ      => W_Type);
               end;
            end if;

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
                        T := Get_Array_Attr (Domain => Domain,
                                             Ty     => Entity (Var),
                                             Attr   => Attr_Id,
                                             Dim    =>
                                               Positive (UI_To_Int (Dim)));

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
                     T := New_Attribute_Expr
                       (Etype (Var), Domain, Attr_Id, Params);

                  when others =>

                     --  All possible cases should have been handled
                     --  before this point.

                     pragma Assert (False);
                     null;
               end case;
            end;

         when Attribute_Loop_Entry =>
            Loop_Entry : declare
               Arg       : constant Node_Id := First (Expressions (Expr));
               Loop_Id   : Entity_Id;
               Loop_Stmt : Node_Id;

            begin
               --  The loop to which attribute Loop_Entry applies is either
               --  identified explicitly in argument, or, if Loop_Entry takes
               --  no arguments, it is the innermost enclosing loop.

               if Present (Arg) then
                  Loop_Id := Entity (Arg);

               --  Climb the parent chain to find the nearest enclosing loop

               else
                  Loop_Stmt := Expr;
                  while Present (Loop_Stmt) loop
                     if Nkind (Loop_Stmt) = N_Loop_Statement then
                        exit;
                     end if;

                     Loop_Stmt := Parent (Loop_Stmt);
                  end loop;

                  Loop_Id := Entity (Identifier (Loop_Stmt));
               end if;

               pragma Assert (Domain /= EW_Pred
                               and then Params.Phase in Generate_VCs);

               T := +Name_For_Loop_Entry (Var, Loop_Id);
            end Loop_Entry;

         when Attribute_Modulus =>
            T := New_Attribute_Expr (Etype (Var), Domain, Attr_Id);

         when Attribute_Mod =>
            declare
               Arg         : constant Node_Id := First (Expressions (Expr));
               Arg_BTyp    : constant W_Type_Id := Base_Why_Type (Arg);
               Target_Type : constant W_Type_Id := Base_Why_Type (Var);

            begin
               --  If the argument is a bitvector we do the modulo on
               --  bitvectors.

               if Why_Type_Is_BitVector (Arg_BTyp) then
                  declare
                     Arg_Modulus : constant Uint := Modulus (Etype (Arg));
                     Var_Modulus : constant Uint := Modulus (Etype (Var));
                     Arg_Expr    : W_Expr_Id;
                     Mod_Expr    : W_Expr_Id;

                  begin
                     --  If the modulus of the argument is greater than the
                     --  value of the modulo operation, then apply the modulo.

                     if Arg_Modulus > Var_Modulus then
                        Arg_Expr :=
                          Transform_Expr (Arg, Arg_BTyp, Domain, Params);

                        --  If the modulo comes from a builtin type, we use
                        --  the modulus valus from Why3 theory.

                        if Get_EW_Type (Var) = EW_Builtin then
                           Mod_Expr :=
                             Insert_Simple_Conversion
                               (Domain => EW_Term,
                                Expr   =>
                                  +MF_BVs (Base_Why_Type (Var)).Two_Power_Size,
                                To     => Arg_BTyp);

                        --  Otherwise, we retrieve the value of the Modulus
                        --  attribute.

                        else
                           Mod_Expr :=
                             New_Attribute_Expr
                               (Etype (Var), Domain, Attribute_Modulus);
                        end if;

                        T := Insert_Simple_Conversion
                               (Domain => EW_Term,
                                Expr   =>
                                  New_Call (Ada_Node => Expr,
                                            Domain   => Domain,
                                            Name     => MF_BVs (Arg_BTyp).Urem,
                                            Args     =>
                                              (1 => Arg_Expr,
                                               2 => Mod_Expr),
                                            Typ      => Arg_BTyp),
                                To => Target_Type);

                     --  If the modulus of the argument is no greater than the
                     --  value of the modulo operation, then simply convert the
                     --  value to the new type.

                     else
                        T := Insert_Simple_Conversion
                               (Domain => EW_Term,
                                Expr   =>
                                  Transform_Expr (Arg, Domain, Params),
                                To     => Target_Type);
                     end if;
                  end;

               --  if not, we do the modulo on integer and convert back

               else
                  T := Insert_Simple_Conversion
                    (Domain => EW_Term,
                     Expr   =>
                       New_Call (Ada_Node => Expr,
                           Domain   => Domain,
                           Name     => M_Int_Div.Mod_Id,
                           Args     =>
                             (1 => Transform_Expr (Arg,
                              EW_Int_Type,
                              Domain,
                              Params),
                              2 =>
                                (if Get_EW_Type (Var) = EW_Builtin then
                                 --  if we're builtin, i.e., not abstract,
                                 --  we use standard modulus from why theory
                                    +MF_BVs (Base_Why_Type (Var)).
                                   Two_Power_Size
                                 else
                                 --  else we refer to the attribute modulus
                                    Insert_Simple_Conversion
                                   (Domain => EW_Term,
                                    Expr   => New_Attribute_Expr
                                      (Etype (Var), Domain, Attribute_Modulus),
                                       To     => EW_Int_Type))),
                                 Typ   => EW_Int_Type),
                     To   => Target_Type);
               end if;
            end;

         when Attribute_Image =>

            --  We generate the expression String.to_string (image_func (expr))

            T := New_Call (Ada_Node => Expr,
                           Domain   => Domain,
                           Name     => +New_Attribute_Expr
                             (Etype (Var), Domain, Attr_Id),
                           Args     =>
                             (1 => Transform_Expr (First (Expressions (Expr)),
                                                   Base_Why_Type (Var),
                                                   Domain,
                              Params)));
            T := New_Call (Ada_Node => Expr,
                           Domain   => Domain,
                           Name     => To_String_Id,
                           Args     => (1 => T),
                           Typ      => EW_Abstract (Standard_String));

         when Attribute_Size =>
            if Nkind (Var) in N_Has_Entity
              and then Present (Entity (Var))
            then
               --  For arrays and records we do not know the exact value of
               --  attribute size, which is decided by the back-end when
               --  generating executable code. Instead, we generate call to an
               --  uninterpreted function, either:
               --
               --  * "value__size", which corresponds to
               --  ** Type'Size in Ada
               --  ** Type'Value_Size in GNAT
               --  ** RM_Size field in GNAT AST
               --
               --  or
               --
               --  * "object__size", which corresponds to
               --  ** Object'Size in Ada
               --  ** Type'Object_Size in GNAT
               --  ** Esize field in GNAT AST

               case Ekind (Entity (Var)) is
                  when Type_Kind =>
                     T := New_Attribute_Expr (Entity (Var), Domain, Attr_Id);

                  when Object_Kind =>
                     if Known_Esize (Etype (Var)) then
                        return New_Integer_Constant (Expr,
                                                     Esize (Etype (Var)));
                     else
                        declare
                           Name : constant W_Identifier_Id :=
                             E_Symb (Etype (Var), WNE_Attr_Object_Size);
                           Arg  : constant W_Expr_Id :=
                             Transform_Expr (Var, Domain, Params);
                        begin
                           return New_Call (Ada_Node => Parent (Var),
                                            Domain   => Domain,
                                            Name     => Name,
                                            Args     => (1 => Arg),
                                            Typ      => EW_Int_Type);
                        end;
                     end if;

                  when others =>
                     Ada.Text_IO.Put_Line ("[Transform_Attr] kind ="
                                           & Node_Kind'Image (Nkind (Var)));
                     raise Not_Implemented;
               end case;
            else
               Ada.Text_IO.Put_Line ("[Transform_Attr] id ="
                                     & Attribute_Id'Image (Attr_Id));
               raise Not_Implemented;
            end if;

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
                           +New_Attribute_Expr (Etype (Var), Domain, Attr_Id);
            begin
               T :=
                 New_Call
                   (Ada_Node => Expr,
                    Domain   => Domain,
                    Name     => Of_String_Id,
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
                  T := New_Ada_Record_Update
                    (Name     => +Prefix_Expr,
                     Domain   => Domain,
                     Updates  =>
                       Transform_Record_Component_Associations
                         (Domain              => Domain,
                          Typ                 => Pref_Typ,
                          Assocs              =>
                            Component_Associations (Aggr),
                          Params              => Params,
                          In_Attribute_Update => True));

                  --  If the target type has a direct or inherited predicate,
                  --  generate a corresponding check.

                  if Domain = EW_Prog
                    and then Has_Predicates (Pref_Typ)
                  then
                     T := +Insert_Predicate_Check (Ada_Node => Expr,
                                                   Check_Ty => Pref_Typ,
                                                   W_Expr   => +T);
                  end if;

               else
                  pragma Assert (Is_Array_Type (Pref_Typ));
                  T := Transform_Aggregate
                    (Params              => Params,
                     Domain              => Domain,
                     Expr                => Aggr,
                     In_Attribute_Update => True);
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
                                 M_Floating.Ceil
                              elsif Attr_Id = Attribute_Floor then
                                 M_Floating.Floor
                              elsif Attr_Id = Attribute_Rounding then
                                M_Floating.Round
                              else M_Floating.Truncate);
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
                      (if Is_Modular_Integer_Type (Ada_Ty) then
                         (if Attr_Id = Attribute_Min
                          then MF_BVs (Base).BV_Min
                          else MF_BVs (Base).BV_Max)
                       else
                         (if Attr_Id = Attribute_Min then M_Int_Minmax.Min
                          else M_Int_Minmax.Max))
                  else (if Attr_Id = Attribute_Min then M_Floating.Min
                        else M_Floating.Max));
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

         when Attribute_Constrained =>

            --  To be able to handle affectations, we put the constrained why
            --  field to false in components of aggregates that have an
            --  unconstrained type with defaulted discriminants.
            --  Thus, on constant objects, we should not use this field to
            --  translate 'Constrained but rather return true directly.

            if Is_Constant_Object (Get_Enclosing_Object (Var)) then
               T := +True_Term;
            else
               declare
                  Ty_Ent : constant Entity_Id :=
                    Unique_Entity (Etype (Var));
               begin
                  declare
                     Why_Expr : constant W_Expr_Id :=
                       Transform_Expr (Var, Domain, Params);
                  begin
                     T := New_Is_Constrained_Access (Domain   => Domain,
                                                     Name     => Why_Expr,
                                                     Ty       => Ty_Ent);
                     if Domain = EW_Prog then
                        T :=
                          +Sequence (New_Ignore (Prog => +Why_Expr), +T);
                     end if;
                  end;
               end;
            end if;

         when Attribute_Address =>
            T := +E_Symb (Entity (Var), WNE_Attr_Address);

         when others =>
            Ada.Text_IO.Put_Line ("[Transform_Attr] id ="
                                  & Attribute_Id'Image (Attr_Id));
            raise Not_Implemented;
      end case;
      return T;
   end Transform_Attr;

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

   function Transform_Compare_Op
     (Op     : N_Op_Compare;
      Ty     : W_Type_Id;
      Domain : EW_Domain)
      return W_Identifier_Id is
   begin
      if Domain = EW_Term then
         if Ty = EW_Int_Type or else Ty = EW_Fixed_Type or else
           Ty = EW_Bool_Type
         then
            case Op is
               when N_Op_Gt => return M_Integer.Bool_Gt;
               when N_Op_Lt => return M_Integer.Bool_Lt;
               when N_Op_Eq => return M_Integer.Bool_Eq;
               when N_Op_Ne => return M_Integer.Bool_Ne;
               when N_Op_Ge => return M_Integer.Bool_Ge;
               when N_Op_Le => return M_Integer.Bool_Le;
            end case;
         elsif Ty = EW_Real_Type then
            case Op is
               when N_Op_Gt => return M_Floating.Bool_Gt;
               when N_Op_Lt => return M_Floating.Bool_Lt;
               when N_Op_Eq => return M_Floating.Bool_Eq;
               when N_Op_Ne => return M_Floating.Bool_Ne;
               when N_Op_Ge => return M_Floating.Bool_Ge;
               when N_Op_Le => return M_Floating.Bool_Le;
            end case;
         elsif Ty = EW_Bool_Type then
            case Op is
               when N_Op_Gt => return M_Boolean.Bool_Gt;
               when N_Op_Lt => return M_Boolean.Bool_Lt;
               when N_Op_Eq => return M_Boolean.Bool_Eq;
               when N_Op_Ne => return M_Boolean.Bool_Ne;
               when N_Op_Ge => return M_Boolean.Bool_Ge;
               when N_Op_Le => return M_Boolean.Bool_Le;
            end case;
         elsif Why_Type_Is_BitVector (Ty) then
            case Op is
               when N_Op_Gt => return MF_BVs (Ty).Bool_Gt;
               when N_Op_Lt => return MF_BVs (Ty).Bool_Lt;
               when N_Op_Eq => return MF_BVs (Ty).Bool_Eq;
               when N_Op_Ne => return MF_BVs (Ty).Bool_Ne;
               when N_Op_Ge => return MF_BVs (Ty).Bool_Ge;
               when N_Op_Le => return MF_BVs (Ty).Bool_Le;
            end case;
         elsif Op in N_Op_Eq | N_Op_Ne then
            return
              New_Identifier
                (Module => Get_Module (Get_Name (Ty)),
                 Name => (if Op = N_Op_Eq then "bool_eq" else "bool_ne"),
                 Typ    => EW_Bool_Type);
         else
            pragma Assert (False);
            return Why_Empty;
         end if;
      elsif Ty = EW_Int_Type
           or else Ty = EW_Bool_Type
           or else Ty = EW_Fixed_Type
      then
         case Op is
            when N_Op_Gt => return Int_Infix_Gt;
            when N_Op_Lt => return Int_Infix_Lt;
            when N_Op_Eq => return Why_Eq;
            when N_Op_Ne => return Why_Neq;
            when N_Op_Ge => return Int_Infix_Ge;
            when N_Op_Le => return Int_Infix_Le;
         end case;
      elsif Ty = EW_Real_Type then
         case Op is
            when N_Op_Gt => return Real_Infix_Gt;
            when N_Op_Lt => return Real_Infix_Lt;
            when N_Op_Eq => return Why_Eq;
            when N_Op_Ne => return Why_Neq;
            when N_Op_Ge => return Real_Infix_Ge;
            when N_Op_Le => return Real_Infix_Le;
         end case;
      elsif Why_Type_Is_BitVector (Ty) then
         case Op is
            when N_Op_Gt => return MF_BVs (Ty).Ugt;
            when N_Op_Lt => return MF_BVs (Ty).Ult;
            when N_Op_Eq => return Why_Eq;
            when N_Op_Ne => return Why_Neq;
            when N_Op_Ge => return MF_BVs (Ty).Uge;
            when N_Op_Le => return MF_BVs (Ty).Ule;
         end case;
      elsif Op = N_Op_Eq then
         return Why_Eq;
      elsif Op = N_Op_Ne then
         return Why_Neq;
      else
         pragma Assert (False);
         return Why_Eq;
      end if;
   end Transform_Compare_Op;

   -----------------------------
   -- Transform_Concatenation --
   -----------------------------

   function Transform_Concatenation
     (Left               : W_Expr_Id;
      Right              : W_Expr_Id;
      Left_Type          : Entity_Id;
      Right_Type         : Entity_Id;
      Return_Type        : Entity_Id;
      Is_Component_Left  : Boolean;
      Is_Component_Right : Boolean;
      Domain             : EW_Domain;
      Ada_Node           : Node_Id) return W_Expr_Id
   is
      Left_Expr  : W_Expr_Id :=  Left;
      Right_Expr : W_Expr_Id :=  Right;
      Args       : W_Expr_Array (1 .. 6);
      Arg_Ind    : Positive := 1;
      T          : W_Expr_Id;
      First_Expr : W_Expr_Id;
      Low_Type   : Entity_Id;
      Exp_Type   : constant Entity_Id :=
        Get_Ada_Node (+Type_Of_Node (Return_Type));
      Comp_Type  : constant W_Type_Id :=
        EW_Abstract (Component_Type (Return_Type));

      function Build_Last_Expr return W_Expr_Id;
      --  build the expression that yields the value of the 'Last attribute
      --  of the concatenation. It is simply
      --    first + length of left opnd + length of right_opnd - 1
      --  Last is always computed with integer (even when dealing with modular)
      --  in order to be coherent with length which is always an integer.

      ---------------------
      -- Build_Last_Expr --
      ---------------------

      function Build_Last_Expr return W_Expr_Id is
         One_Term : constant W_Expr_Id :=
           New_Discrete_Constant (Value => Uint_1,
                                  Typ   => EW_Int_Type);
         Left_Length : constant W_Expr_Id :=
           (if Is_Component_Left
            then One_Term
            else
               Build_Length_Expr
              (Domain => Domain,
               First => Get_Array_Attr (Domain, Left_Expr, Attribute_First, 1),
               Last => Get_Array_Attr (Domain, Left_Expr, Attribute_Last, 1),
               Typ => EW_Int_Type));
         Right_Length : constant W_Expr_Id :=
           (if Is_Component_Right
            then One_Term
            else
               Build_Length_Expr
              (Domain => Domain,
               First => Get_Array_Attr
                 (Domain, Right_Expr, Attribute_First, 1),
               Last => Get_Array_Attr (Domain, Right_Expr, Attribute_Last, 1),
               Typ => EW_Int_Type));
      begin
         return
           +New_Discrete_Substract
           (Domain,
            New_Discrete_Add
              (Domain,
               First_Expr,
               New_Discrete_Add
                 (Domain,
                  Left_Length,
                  Right_Length),
               EW_Int_Type),
            One_Term);
      end Build_Last_Expr;

   --  Start of processing for Transform_Concatenation

   begin

      --  Step 1: introduce temps for left and right

      Left_Expr := New_Temp_For_Expr (Left_Expr);
      Right_Expr := New_Temp_For_Expr (Right_Expr);

      --  Step 2: compute the lower bound of the concatenation
      --  See RM 4.5.3(6-7) for the rules. The test here is taken from
      --  Expand_Concatenate in exp_ch4.adb.

      Low_Type := First_Subtype (Root_Type (Base_Type (Return_Type)));

      if Is_Static_Array_Type (Low_Type) then
         First_Expr := Get_Array_Attr (Domain, Low_Type, Attribute_First, 1);

      elsif Is_Component_Left then
         First_Expr :=
           New_Attribute_Expr
             (Nth_Index_Type (Return_Type, 1),
              Domain, Attribute_First, Body_Params);

      else
         First_Expr := Get_Array_Attr (Domain, Left_Expr, Attribute_First, 1);
      end if;

      --  Step 3: do to the actual concatenation
      --  We prepare the arguments to the concat call. If one of the sides is
      --  a component, need to possibly convert it to the right type (think of
      --  integer literals, need to convert to Standard__Integer)

      if Is_Component_Left then
         Args (1) := New_Singleton_Call (Ada_Node,
                                         Domain,
                                         Insert_Simple_Conversion
                                           (Ada_Node => Ada_Node,
                                            Domain => Domain,
                                            Expr   => Left_Expr,
                                            To     => Comp_Type),
                                         First_Expr);
         Args (2) := First_Expr;
         Args (3) := First_Expr;
         Arg_Ind := 4;
      else
         Add_Array_Arg (Domain, Args, Left_Expr, Arg_Ind);
      end if;

      if Is_Component_Right then
         declare
            One_Term : constant W_Expr_Id :=
              New_Discrete_Constant (Value => Uint_1,
                                     Typ => Nth_Index_Rep_Type_No_Bool
                                       (Low_Type, 1));
         begin
            Args (4) := New_Singleton_Call
              (Ada_Node,
               Domain,
               Insert_Simple_Conversion (Domain => Domain,
                                         Expr   => Right_Expr,
                                         To     => Comp_Type),
               One_Term);
            Args (5) := One_Term;
            Args (6) := One_Term;
         end;
      else
         Add_Array_Arg (Domain, Args, Right_Expr, Arg_Ind);
      end if;

      --  We build the call to concat

      T := New_Concat_Call (Domain, Args, Type_Of_Node (Return_Type));

      --  Depending on the lower bound of the concat, the object may not be
      --  slided correctly, because the concat operator in Why assumes that
      --  the new low bound is the one of the left opnd. Correct that.

      if not Is_Component_Left
        and then Is_Static_Array_Type (Low_Type)
      then
         T :=
           New_Call
             (Domain => Domain,
              Name   => Get_Array_Theory (Return_Type).Slide,
              Args   =>
                (1 => T,
                 2 => Get_Array_Attr (Domain, Left_Expr, Attribute_First, 1),
                 3 => First_Expr),
              Typ    => Type_Of_Node (Return_Type));
      end if;

      --  Now the expression T is of the Why array type. We need to convert it
      --  to the type of the concatenation expression. Whenever this type is
      --  constrained, we are done. In other cases, we need to convert to the
      --  unconstrained representation. This situation also requires a range
      --  check.

      if not Is_Static_Array_Type (Return_Type) then
         declare
            Target    : constant Entity_Id := Nth_Index_Type (Exp_Type, 1);
            Last_Expr : W_Expr_Id := Build_Last_Expr;
         begin
            if Domain = EW_Prog then
               Last_Expr :=
                 Insert_Simple_Conversion
                   (Domain         => EW_Prog,
                    Expr           =>
                      +Do_Range_Check (Ada_Node   => Ada_Node,
                                       Ty         => Target,
                                       W_Expr     => Last_Expr,
                                       Check_Kind => RCK_Range),
                    To             => Get_Type (First_Expr));
            end if;
            T := Array_Convert_From_Base
              (Domain => Domain,
               Target => Exp_Type,
               Ar     => T,
               First  => First_Expr,
               Last   => Last_Expr);
         end;
      else
         pragma Assert (False);
      end if;

      --  If the Left operand is a null array then concatenate returns Right
      --  We handle this case statically, if we can

      if not Is_Component_Left then

         --  if the left type is not static, handle things in Why

         if not Is_Static_Array_Type (Left_Type) then
            declare
               Right_First : constant W_Expr_Id :=
                 (if Is_Component_Right then
                     New_Attribute_Expr
                    (Nth_Index_Type (Return_Type, 1),
                     Domain,
                     Attribute_First,
                     Body_Params)
                  else
                     Get_Array_Attr (Domain, Right_Expr, Attribute_First, 1));
               Right_Last : constant W_Expr_Id :=
                 (if Is_Component_Right then Right_First
                  else Get_Array_Attr (Domain, Right_Expr, Attribute_Last, 1));
               Right_Op    : W_Expr_Id :=
                 (if Is_Component_Right then
                     New_Singleton_Call
                    (Return_Type,
                     Domain,
                     Insert_Simple_Conversion (Domain => Domain,
                                               Expr   => Right_Expr,
                                               To     => Comp_Type),
                     Right_First)
                  elsif Is_Static_Array_Type (Right_Type)
                  or (Get_Type_Kind (Get_Type (Right_Expr)) = EW_Split)
                  then Right_Expr
                  else Array_Convert_To_Base (Domain => Domain,
                                              Ar     => Right_Expr));
               Condition   : constant W_Expr_Id :=
                 New_Call
                   (Domain   => EW_Pred,
                    Typ      => EW_Bool_Type,
                    Name     => Why_Eq,
                    Args     =>
                      (1 =>
                       Get_Array_Attr (Domain, Left_Expr, Attribute_Length, 1),
                       2 => New_Integer_Constant (Value => Uint_0)));
            begin
               if not Is_Static_Array_Type (Return_Type) then
                  Right_Op := Array_Convert_From_Base (Domain => Domain,
                                                       Target => Exp_Type,
                                                       Ar     => Right_Op,
                                                       First  => Right_First,
                                                       Last   => Right_Last);
               end if;

               T := New_Conditional
                 (Domain      => Domain,
                  Condition   => Condition,
                  Then_Part   => Right_Op,
                  Else_Part   => T,
                  Typ         => Get_Type (T));
            end;

         --  here we know that the type is static, check if length is 0
         --  ??? here we don't use T that we built earlier, move this code
         --  before actually doing the concatenation

         elsif Static_Array_Length (Left_Type, 1) = Uint_0 then
            declare
               Right_First : constant W_Expr_Id :=
                 (if Is_Component_Right then
                       New_Attribute_Expr
                    (Nth_Index_Type (Return_Type, 1),
                     Domain,
                     Attribute_First,
                     Body_Params)
                  else Get_Array_Attr
                    (Domain, Right_Expr, Attribute_First, 1));
            begin
               T :=
                 (if Is_Component_Right then
                     New_Singleton_Call
                    (Return_Type,
                     Domain,
                     Insert_Simple_Conversion (Domain => Domain,
                                               Expr   => Right_Expr,
                                               To     => Comp_Type),
                     Right_First)
                  elsif Is_Static_Array_Type (Right_Type) then
                       Right_Expr
                  else Array_Convert_To_Base (Domain => Domain,
                                              Ar     => Right_Expr));
            end;

         --  here we know that the lhs is not null, so T remains unchanged

         else
            null;
         end if;

      end if;

      --  Step 3: bind the introduced names if any, and return

      T := Binding_For_Temp (Domain  => Domain,
                             Tmp     => Left_Expr,
                             Context => T);
      T :=  Binding_For_Temp (Domain  => Domain,
                             Tmp     => Right_Expr,
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

      function Get_Base_Type (N : Node_Id) return Entity_Id is
         Ent : constant Entity_Id := Defining_Identifier (N);
      begin
         --  Full type declarations can only require checks when they are
         --  scalar types, and then only when the range is non-static.

         if Nkind (N) = N_Full_Type_Declaration then
            if Is_Scalar_Type (Ent) then
               if Is_OK_Static_Range (Get_Range (Ent)) then
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

   --  Start of processing for Transform_Declaration

   begin
      case Nkind (Decl) is
         when N_Object_Declaration =>

            --  we can ignore task declarations

            if Is_Task_Type (Etype (Defining_Entity (Decl))) then
               return R;
            end if;

            --  non scalar object declaration should not appear before the
            --  loop invariant in a loop.

            pragma Assert
              (not Is_In_Loop_Initial_Statements
               or else (Is_Scalar_Type (Etype (Defining_Entity (Decl)))
                 and then Is_Loop_Entity (Defining_Entity (Decl)))
               or else Is_Actions_Entity (Defining_Entity (Decl)));

            R := Assignment_Of_Obj_Decl (Decl);

            if not Is_Partial_View (Defining_Identifier (Decl)) then
               declare
                  Lvalue : Entity_Id := Defining_Identifier (Decl);
               begin
                  if Is_Full_View (Lvalue) then
                     Lvalue := Partial_View (Lvalue);
                  end if;

                  R := Sequence
                    (R,
                     Assume_Dynamic_Invariant
                       (Expr        =>
                          +Transform_Identifier (Expr   => Lvalue,
                                                 Ent    => Lvalue,
                                                 Domain => EW_Term,
                                                 Params => Body_Params),
                        Ty          => Etype (Lvalue),
                        Initialized => Present (Expression (Decl)),
                        Only_Var    => False));
               end;
            end if;

            if Is_Protected_Type (Etype (Defining_Identifier (Decl)))
              and then Requires_Interrupt_Priority
                (Etype (Defining_Identifier (Decl)))
            then
               declare
                  Lvalue : Entity_Id := Defining_Identifier (Decl);
                  P      : constant Node_Id :=
                    Get_Priority_Or_Interrupt_Priority
                      (Etype (Defining_Identifier (Decl)));
               begin
                  if Is_Full_View (Lvalue) then
                     Lvalue := Partial_View (Lvalue);
                  end if;

                  --  If no priority was specified, the default priority
                  --  respects the ceiling priority.

                  if Present (P) then

                     --  Store the value of Decl's discriminants in the
                     --  symbol table

                     declare
                        Num_Discrs : constant Natural :=
                          (if Has_Discriminants (Etype (Lvalue)) then
                              Natural (Number_Discriminants (Etype (Lvalue)))
                           else 0);
                        Discr_Ids  : W_Identifier_Array (1 .. Num_Discrs);
                        Discr_Vals : W_Expr_Array (1 .. Num_Discrs);
                        D          : Node_Id :=
                          First_Discriminant (Etype (Lvalue));
                        P_Expr     : W_Expr_Id;
                     begin
                        Ada_Ent_To_Why.Push_Scope (Symbol_Table);

                        for I in Discr_Ids'Range loop
                           while Is_Completely_Hidden (D) loop
                              Next_Discriminant (D);
                           end loop;
                           pragma Assert (Present (D));

                           Discr_Ids (I) :=
                             New_Temp_Identifier
                               (Typ => EW_Abstract (Etype (D)));

                           Insert_Entity (Discriminal (D), Discr_Ids (I));

                           Discr_Vals (I) :=
                             New_Ada_Record_Access
                               (Ada_Node => Empty,
                                Domain   => EW_Term,
                                Name     =>
                                  +Transform_Identifier
                                  (Expr   => Lvalue,
                                   Ent    => Lvalue,
                                   Domain => EW_Term,
                                   Params => Body_Params),
                                Field    => D,
                                Ty       => Etype (Lvalue));

                           Next_Discriminant (D);
                        end loop;
                        pragma Assert (No (D));

                        P_Expr := Transform_Expr
                          (Expr          => P,
                           Domain        => EW_Term,
                           Params        => Body_Params,
                           Expected_Type => EW_Int_Type);

                        for I in Discr_Ids'Range loop
                           P_Expr := New_Typed_Binding
                             (Domain   => EW_Term,
                              Name     => Discr_Ids (I),
                              Def      => Discr_Vals (I),
                              Context  => P_Expr);
                        end loop;

                        R := Sequence
                          (R,
                           New_Located_Assert
                             (Ada_Node => Decl,
                              Pred     => +New_Range_Expr
                                (Domain => EW_Pred,
                                 Low    => +New_Constant
                                   (UI_From_Int (Int
                                    (Interrupt_Priority'First))),
                                 High   => +New_Constant
                                   (UI_From_Int (Int
                                    (Interrupt_Priority'Last))),
                                 Expr   => P_Expr),
                              Reason   => VC_Ceiling_Interrupt,
                              Kind     => EW_Check));

                        Ada_Ent_To_Why. Pop_Scope (Symbol_Table);
                     end;
                  end if;
               end;
            end if;

            --  check that no attach_handler expression of the protected
            --  object corresponds to a reserved signal

            if Is_Protected_Type (Etype (Defining_Entity (Decl))) then
               R := Sequence
                 (R,
                  Compute_Attach_Handler_Check
                    (Etype (Defining_Entity (Decl)), Body_Params));
            end if;

         when N_Subtype_Declaration | N_Full_Type_Declaration =>
            declare
               Ent  : constant Entity_Id := Unique_Defining_Entity (Decl);
               Base : Entity_Id := Get_Base_Type (Decl);
            begin
               if Present (Base) then
                  Base := Retysp (Base);
               end if;

               if Entity_In_SPARK (Ent) then
                  case Ekind (Ent) is
                  when Scalar_Kind =>
                     R := Check_Scalar_Range (Params   => Body_Params,
                                              N        => Ent,
                                              Base     => Base);

                  when Array_Kind =>
                     declare
                        Index       : Node_Id;
                        Index_Base  : Entity_Id;
                     begin
                        --  For each discrete_subtype_definition that is a
                        --  non-static subtype_indication, we generate a check
                        --  that the range_constraint is compatible with the
                        --  subtype.

                        Index := First_Index (Ent);
                        while Present (Index) loop
                           if Nkind (Index) = N_Subtype_Indication then
                              if Comes_From_Source (Index) then
                                 R := Sequence
                                   (Check_Subtype_Indication
                                      (Params   => Body_Params,
                                       N        => Index,
                                       Sub_Type => Etype (Index)),
                                    R);
                              end if;
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
                              if Comes_From_Source (Index) then
                                 R := Sequence
                                   (Check_Scalar_Range
                                      (Params   => Body_Params,
                                       N        => Etype (Index),
                                       Base     => Etype (Index_Base)),
                                    R);
                              end if;
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
                             and then Comes_From_Source (Typ)
                           then
                              R := Sequence
                                (Check_Subtype_Indication
                                   (Params   => Body_Params,
                                    N        => Typ,
                                    Sub_Type => Etype (Comp)),
                                 R);
                           end if;
                           Next_Component (Comp);
                        end loop;
                     end;

                  when Private_Kind
                     | E_Class_Wide_Type
                     | E_Class_Wide_Subtype
                     | E_Protected_Type
                     | E_Protected_Subtype
                     | E_Task_Type
                     | E_Task_Subtype
                     =>
                     null;

                  when others =>
                     Ada.Text_IO.Put_Line
                       ("[Transform_Declaration] ekind ="
                        & Entity_Kind'Image (Ekind (Ent)));
                     raise Not_Implemented;
                  end case;
               end if;
            end;

         when N_Pragma =>
            R := Transform_Pragma (Decl, Force => False);

         when N_Raise_xxx_Error | N_Raise_Statement =>
            R := Transform_Raise (Decl);

         when N_Package_Declaration =>

            --  Assume dynamic property of local variables.
            --  ??? What about local variables of nested packages?

            declare
               E        : constant Entity_Id := Unique_Defining_Entity (Decl);
               Var_Set  : constant Name_Sets.Set :=
                 GG_Get_Local_Variables (To_Entity_Name (E));
               --  Local variables declared in E.

               Init_Map : constant Dependency_Maps.Map :=
                 Parse_Initializes (Get_Pragma (E, Pragma_Initializes),
                                    E,
                                    Get_Flow_Scope (E));
               Init_Set : Name_Sets.Set;
               --  Local Variables initialized by E.
            begin

               --  First, get initialized variables for Initializes aspect.

               for Cu in Init_Map.Iterate loop
                  declare
                     S      : constant Flow_Id_Sets.Set :=
                       Expand_Abstract_State (Dependency_Maps.Key (Cu),
                                              Erase_Constants => False);
                     E_Name : Entity_Name;
                     Entity : Entity_Id;
                  begin
                     for X of S loop
                        case X.Kind is
                        when Direct_Mapping | Record_Field =>
                           E_Name := To_Entity_Name (X.Node);
                        when Magic_String =>
                           E_Name := X.Name;
                        when Null_Value | Synthetic_Null_Export =>
                           raise Program_Error;
                        end case;

                        Entity := Find_Entity (E_Name);

                        --  Assume declaration of X

                        if Present (Entity)
                          and then Nkind (Entity) in N_Entity
                          and then (Is_Object (Entity)
                                    or else Is_Named_Number (Entity))
                          and then Entity_In_SPARK (Entity)
                          and then Ada_Ent_To_Why.Has_Element
                            (Symbol_Table, Entity)
                        then
                           Assume_Declaration_Of_Entity
                             (E             => Entity,
                              Params        => Body_Params,
                              Initialized   => True,
                              Top_Predicate => True,
                              Context       => R);
                        end if;

                        --  Store it in Init_Set so that we do not declare it
                        --  again.

                        Init_Set.Include (E_Name);
                     end loop;
                  end;
               end loop;

               --  Then also assume dynamic property of unitialized variables.

               for X of Var_Set loop

                  --  Do nothing if the variable has already been declared.

                  if not Init_Set.Contains (X) then
                     declare
                        Entity : constant Entity_Id := Find_Entity (X);
                     begin

                        --  Assume declaration of X

                        if Present (Entity)
                          and then Nkind (Entity) in N_Entity
                          and then (Is_Object (Entity)
                                    or else Is_Named_Number (Entity))
                          and then Entity_In_SPARK (Entity)
                          and then Ada_Ent_To_Why.Has_Element
                            (Symbol_Table, Entity)
                        then
                           Assume_Declaration_Of_Entity
                             (E             => Entity,
                              Params        => Body_Params,
                              Initialized   => False,
                              Top_Predicate => True,
                              Context       => R);
                        end if;
                     end;
                  end if;
               end loop;
            end;

            --  Assume initial condition

            declare
               Init_Cond  : constant Node_Id :=
                 Get_Pragma (Unique_Defining_Entity (Decl),
                             Pragma_Initial_Condition);
            begin
               if Present (Init_Cond) then
                  declare
                     Expr : constant Node_Id :=
                       Expression (First (Pragma_Argument_Associations
                                   (Init_Cond)));
                  begin
                     R := Sequence
                       (R,
                        New_Assume_Statement
                          (Pred => +Transform_Expr
                               (Expr, EW_Bool_Type, EW_Pred, Body_Params)));
                  end;
               end if;
            end;

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

   -------------------------------------
   -- Transform_Declarations_For_Body --
   -------------------------------------

   function Transform_Declarations_For_Body
     (L : List_Id) return W_Prog_Id
   is
      Cur_Decl : Node_Id := First (L);
      Result   : W_Prog_Id := New_Void;
   begin
      while Present (Cur_Decl)
        and then Declaration_Is_Associated_To_Parameter (Cur_Decl)
      loop
         Next (Cur_Decl);
      end loop;
      while Present (Cur_Decl) loop
         Result := Sequence (Result, Transform_Declaration (Cur_Decl));
         Next (Cur_Decl);
      end loop;
      return Result;
   end Transform_Declarations_For_Body;

   ---------------------------------------
   -- Transform_Declarations_For_Params --
   ---------------------------------------

   function Transform_Declarations_For_Params
     (L : List_Id) return W_Prog_Id
   is
      Cur_Decl : Node_Id := First (L);
      Result   : W_Prog_Id := New_Void;
   begin
      while  Present (Cur_Decl)
        and then Declaration_Is_Associated_To_Parameter (Cur_Decl)
      loop
         Result := Sequence (Result, Transform_Declaration (Cur_Decl));
         Next (Cur_Decl);
      end loop;
      return Result;
   end Transform_Declarations_For_Params;

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
         R := Range_Expr (Choice, Expr, Domain, Params);

         --  In programs, we generate a check that the range_constraint of a
         --  subtype_indication is compatible with the given subtype.

         if Domain = EW_Prog then
            pragma Assert (Present (Choice_Type));
            R := +Sequence
              (Check_Scalar_Range (Params   => Params,
                                   N        => Choice,
                                   Base     => Choice_Type),
               +R);
         end if;

      else
         R := New_Comparison
           (Symbol => Why_Eq,
            Left   => Expr,
            Right  => Transform_Expr
              (Expr          => Choice,
               Expected_Type => Base_Why_Type_No_Bool (Choice),
               Domain        => Subdomain,
               Params        => Params),
            Domain => Domain);

         --  In programs, we generate a check that the non-static value of a
         --  choice belongs to the given subtype.

         if Domain = EW_Prog
           and then (not Is_OK_Static_Expression (Choice)
                     or else not Has_Static_Scalar_Subtype (Choice_Type))
         then
            pragma Assert (Present (Choice_Type));
            R := +Sequence
                   (+New_Ignore (Prog =>
                      Do_Range_Check
                        (Ada_Node   => Choice,
                         Ty         => Choice_Type,
                         W_Expr     =>
                           Transform_Expr (Expr          => Choice,
                                           Expected_Type =>
                                           Base_Why_Type_No_Bool (Choice),
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
               (Ada_Node => Etype (Expr),
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
        (if Nkind (Expr) in N_Op_Multiply | N_Op_Divide
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
        and then Local_Params.Gen_Marker
        and then Is_Terminal_Node (Expr)
      then
         Pretty_Label := New_Sub_VC_Marker (Expr);
         Local_Params.Gen_Marker := False;
      end if;

      --  Expressions that cannot be translated to predicates directly are
      --  translated to (boolean) terms, and compared to "True".

      if Domain = EW_Pred and then
         not (Nkind (Expr) in N_Op_Compare | N_Op_Not | N_Op_And | N_And_Then
         | N_Op_Or | N_Or_Else | N_In | N_If_Expression |
         N_Quantified_Expression | N_Case_Expression) and then
         not (Nkind (Expr) in N_Identifier | N_Expanded_Name and then
              Ekind (Entity (Expr)) in E_Enumeration_Literal and then
              (Entity (Expr) = Standard_True or else
               Entity (Expr) = Standard_False))
      then
         T := +Pred_Of_Boolean_Term
                 (+Transform_Expr (Expr, EW_Bool_Type, EW_Term, Local_Params));

      elsif Domain /= EW_Pred and then
        Is_Discrete_Type (Expr_Type) and then
        Compile_Time_Known_Value (Expr)
      then

         --  Optimization: if we have a discrete value that is statically
         --  known, use the static value.

         T := New_Discrete_Constant
           (Value => Expr_Value (Expr),
            Typ   => Base_Why_Type_No_Bool (Expr_Type));
      else
         case Nkind (Expr) is
         when N_Aggregate =>
            declare
               Expr_Type : constant Entity_Id := Type_Of_Node (Expr);
            begin
               if Is_Record_Type (Expr_Type) then
                  pragma Assert (Is_Empty_List (Expressions (Expr)));

                  --  If the type is an empty record in Why (no tag, no field,
                  --  no discriminant), we use the dummy node of the root type
                  --  here.

                  if Count_Why_Top_Level_Fields (Expr_Type) = 0 then
                     return
                       +E_Symb (Unique_Entity (Root_Record_Type (Expr_Type)),
                                WNE_Dummy);
                  else
                     declare
                        Assocs : constant W_Field_Association_Array :=
                          Transform_Record_Component_Associations
                            (Domain,
                             Expr_Type,
                             Component_Associations (Expr),
                             Local_Params);
                        Num_Discrs : constant Natural :=
                          Count_Non_Inherited_Discriminants
                            (Component_Associations (Expr));
                     begin
                        T :=
                          New_Ada_Record_Aggregate
                            (Ada_Node     => Expr,
                             Domain       => Domain,
                             Discr_Assocs => Assocs (1 .. Num_Discrs),
                             Field_Assocs =>
                               Assocs (Num_Discrs + 1 .. Assocs'Last),
                             Ty           => Expr_Type);
                     end;
                  end if;
               else
                  pragma Assert
                    (Is_Array_Type (Expr_Type) or else
                     Is_String_Type (Expr_Type));

                  T := Transform_Aggregate (Params => Local_Params,
                                            Domain => Domain,
                                            Expr   => Expr);
               end if;
            end;

         when N_Extension_Aggregate =>
            declare
               Expr_Type : constant Entity_Id := Type_Of_Node (Expr);
               Assocs : constant W_Field_Association_Array :=
                 Transform_Record_Component_Associations
                   (Domain,
                    Expr_Type,
                    Component_Associations (Expr),
                    Local_Params);

               --  Check that the derived type does not introduce any
               --  discriminant, which is currently not allowed in SPARK,
               --  and not supported by the current scheme which defined
               --  all discriminant types in the root record type.

               Num_Discrs : constant Natural :=
                 Count_Non_Inherited_Discriminants
                   (Component_Associations (Expr));

               pragma Assert (Num_Discrs = 0);

               --  Use the base type of the ancestor part as intermediate type
               --  to which the ancestor is converted if needed before copying
               --  its fields to the extension aggregate. This takes care
               --  of generating a dummy value for unused components in a
               --  discriminant record, if needed.

               Prefix_Ty : constant Entity_Id :=
                 Unique_Entity (Etype (Ancestor_Part (Expr)));
               Anc_Ty : constant Entity_Id :=
                 (if Ekind (Prefix_Ty) in E_Record_Subtype |
                                          E_Record_Subtype_With_Private
                  then
                    Retysp (Etype (Prefix_Ty))
                  else
                    Prefix_Ty);

               Anc_Expr : constant W_Expr_Id :=
                 Transform_Expr (Ancestor_Part (Expr),
                                 Type_Of_Node (Anc_Ty),
                                 Domain,
                                 Params);
               Tmp : constant W_Expr_Id := New_Temp_For_Expr (Anc_Expr);
               Anc_Num_Discrs : constant Natural :=
                 (if Has_Discriminants (Anc_Ty) then
                    Natural (Number_Discriminants (Anc_Ty))
                  else 0);
               pragma Assert (if Has_Private_Ancestor (Anc_Ty)
                              then Has_Private_Ancestor (Expr_Type));
               Anc_Num_Fields : constant Natural :=
                 Count_Why_Regular_Fields (Expr_Type) - Assocs'Length - 1;

               --  The number of missing fields from the aggregate minus the
               --  extension.

               Anc_Discr_Assocs : W_Field_Association_Array
                                    (1 .. Anc_Num_Discrs);
               Anc_Field_Assocs : W_Field_Association_Array
                                    (1 .. Anc_Num_Fields);

            begin
               Generate_Associations_From_Ancestor
                 (Domain       => Domain,
                  Expr         => Tmp,
                  Anc_Ty       => Anc_Ty,
                  Ty           => Expr_Type,
                  Discr_Assocs => Anc_Discr_Assocs,
                  Field_Assocs => Anc_Field_Assocs);
               T :=
                 New_Ada_Record_Aggregate
                   (Domain       => Domain,
                    Discr_Assocs => Anc_Discr_Assocs,
                    Field_Assocs => Anc_Field_Assocs & Assocs,
                    Ty           => Expr_Type);
               T := Binding_For_Temp (Domain   => Domain,
                                      Tmp      => Tmp,
                                      Context  => T);
            end;

         when N_Slice =>
            T := Transform_Slice (Local_Params, Domain, Expr);

         when N_Integer_Literal =>
            T :=
              New_Integer_Constant
                (Ada_Node => Expr,
                 Value    => Intval (Expr));

         when N_Real_Literal =>

            --  Literals of fixed-point type are directly translated into the
            --  integer that represents them in the corresponding fixed-point
            --  type.

            if Is_Fixed_Point_Type (Etype (Expr)) then
               T := New_Fixed_Constant
                      (Ada_Node => Expr,
                       Value    => Corresponding_Integer_Value (Expr));

            --  Note: although the original node for a real literal might
            --  be closer to the source code expression of the value, this
            --  original node should not be used for transforming the node
            --  into Why. Indeed, a source float literal in Ada might not be
            --  representable in machine, in which case the frontend rewrites
            --  the value into a machine representable value (respecting
            --  the Ada RM rules, so getting the closest representable
            --  floating-point value).

            --  The procedure printing this node in Why takes care of putting
            --  the value in a suitable form for provers. In particular, we
            --  want to avoid printing divisions between real numbers, which
            --  provers don't handle well, even when the division can be
            --  expressed exactly as a decimal number.

            else
               T := New_Real_Constant (Ada_Node => Expr,
                                       Value    => Realval (Expr));
            end if;

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
            elsif Is_Array_Type (Etype (Left_Opnd (Expr))) then
               T := New_Op_Expr
                 (Op          => Nkind (Expr),
                  Left        =>
                    Transform_Expr (Left_Opnd (Expr),
                      (if Domain = EW_Pred then EW_Term else Domain),
                      Local_Params),
                  Right       =>
                    Transform_Expr (Right_Opnd (Expr),
                      (if Domain = EW_Pred then EW_Term else Domain),
                    Local_Params),
                  Left_Type   => Etype (Left_Opnd (Expr)),
                  Right_Type  => Etype (Right_Opnd (Expr)),
                  Return_Type => Expr_Type,
                  Domain      => Domain,
                  Ada_Node    => Expr);
            else
               declare
                  Left  : constant Node_Id := Left_Opnd (Expr);
                  Right : constant Node_Id := Right_Opnd (Expr);

                  Subdomain : constant EW_Domain :=
                    (if Domain = EW_Pred then EW_Term else Domain);

                  BT        : constant W_Type_Id :=
                    Base_Why_Type (Left, Right);
                  Left_Arg  : constant W_Expr_Id :=
                    Transform_Expr (Left, BT, Subdomain,
                                    Local_Params);
                  Right_Arg : constant W_Expr_Id :=
                    Transform_Expr (Right, BT, Subdomain,
                                    Local_Params);

               begin
                  T := New_Op_Expr
                    (Op          => Nkind (Expr),
                     Left        => Left_Arg,
                     Right       => Right_Arg,
                     Left_Type   => Etype (Left),
                     Right_Type  => Etype (Right),
                     Return_Type => Expr_Type,
                     Domain      => Domain,
                     Ada_Node    => Expr);
               end;
            end if;

         when N_Op_Minus | N_Op_Plus | N_Op_Abs =>

            --  unary minus
            --  unary plus

            declare
               Right : constant Node_Id := Right_Opnd (Expr);
            begin
               T := New_Op_Expr
                 (Op          => Nkind (Expr),
                  Right       =>
                    Transform_Expr (Right, Base_Why_Type (Right), Domain,
                    Local_Params),
                  Right_Type  => Etype (Right),
                  Return_Type => Expr_Type,
                  Domain      => Domain,
                  Ada_Node    => Expr);
            end;

         when N_Op_Add | N_Op_Subtract =>
            --  The arguments of arithmetic functions have to be of base
            --  scalar types.
            declare
               Left  : constant Node_Id := Left_Opnd (Expr);
               Right : constant Node_Id := Right_Opnd (Expr);
               Base  : constant W_Type_Id := Base_Why_Type (Left, Right);
            begin
               T := New_Op_Expr
                 (Op          => Nkind (Expr),
                  Left        => Transform_Expr (Left,
                    Base,
                    Domain,
                    Local_Params),
                  Right       => Transform_Expr (Right,
                    Base,
                    Domain,
                    Local_Params),
                  Left_Type   => Etype (Left),
                  Right_Type  => Etype (Right),
                  Return_Type => Expr_Type,
                  Domain      => Domain,
                  Ada_Node    => Expr);
            end;

         when N_Op_Multiply | N_Op_Divide =>
            --  The arguments of arithmetic functions have to be of base
            --  scalar types.
            declare
               Left  : constant Node_Id := Left_Opnd (Expr);
               Right : constant Node_Id := Right_Opnd (Expr);
               L_Type, R_Type : W_Type_Id;
               L_Why, R_Why : W_Expr_Id;
            begin
               if Has_Fixed_Point_Type (Etype (Left))
                 and then Has_Fixed_Point_Type (Etype (Right))
               then
                  L_Type := EW_Fixed_Type;
                  R_Type := EW_Fixed_Type;

               elsif Has_Fixed_Point_Type (Etype (Left)) then
                  L_Type := EW_Fixed_Type;
                  R_Type := EW_Int_Type;

               elsif Nkind (Expr) = N_Op_Multiply
                 and then Has_Fixed_Point_Type (Etype (Right))
               then
                  L_Type := EW_Int_Type;
                  R_Type := EW_Fixed_Type;

               else
                  L_Type := Base_Why_Type (Left, Right);
                  R_Type := Base_Why_Type (Left, Right);
               end if;

               L_Why :=
                 Transform_Expr (Left,
                                 L_Type,
                                 Domain,
                                 Local_Params);
               R_Why :=
                 Transform_Expr (Right,
                                 R_Type,
                                 Domain,
                                 Local_Params);

               T := New_Op_Expr
                 (Op          => Nkind (Expr),
                  Left        => L_Why,
                  Right       => R_Why,
                  Left_Type   => Etype (Left),
                  Right_Type  => Etype (Right),
                  Return_Type => Expr_Type,
                  Domain      => Domain,
                  Ada_Node    => Expr);
            end;

         when N_Op_Rem | N_Op_Mod =>
            declare
               Left  : constant Node_Id := Left_Opnd (Expr);
               Right : constant Node_Id := Right_Opnd (Expr);
               Base  : constant W_Type_Id := Base_Why_Type (Left, Right);
            begin

               T := New_Op_Expr
                 (Op          => Nkind (Expr),
                  Left        => Transform_Expr (Left,
                    Base,
                    Domain,
                    Local_Params),
                  Right       => Transform_Expr (Right,
                    Base,
                    Domain,
                    Local_Params),
                  Left_Type   => Etype (Left),
                  Right_Type  => Etype (Right),
                  Return_Type => Expr_Type,
                  Domain      => Domain,
                  Ada_Node    => Expr);
            end;

         when N_Op_Expon =>
            declare
               Left    : constant Node_Id := Left_Opnd (Expr);
               Right   : constant Node_Id := Right_Opnd (Expr);
               W_Right : constant W_Expr_Id :=
                 Transform_Expr (Right,
                                 EW_Int_Type,
                                 Domain,
                                 Local_Params);
            begin
               T := New_Op_Expr
                 (Op          => Nkind (Expr),
                  Left        => Transform_Expr (Left,
                    Base_Why_Type (Left),
                    Domain,
                    Local_Params),
                  Right       => W_Right,
                  Left_Type   => Etype (Left),
                  Right_Type  => Etype (Right),
                  Return_Type => Expr_Type,
                  Domain      => Domain,
                  Ada_Node    => Expr);
            end;

         when N_Op_Not =>
            if Is_Array_Type (Etype (Right_Opnd (Expr))) then
               declare
                  Subdomain : constant EW_Domain :=
                    (if Domain = EW_Pred then EW_Term else Domain);
               begin
                     T := New_Op_Expr
                       (Op          => Nkind (Expr),
                        Right       => Transform_Expr
                          (Right_Opnd (Expr), Subdomain, Params),
                        Right_Type  => Etype (Right_Opnd (Expr)),
                        Return_Type => Expr_Type,
                        Domain      => Domain,
                        Ada_Node    => Expr);
               end;

            elsif Is_Modular_Integer_Type (Expr_Type) then
               declare
                  Base : constant W_Type_Id := Base_Why_Type (Expr_Type);
               begin
                  T := New_Call (Ada_Node => Expr,
                                 Domain   => Domain,
                                 Name     => MF_BVs (Base).BW_Not,
                                 Args     => (1 => Transform_Expr
                                                     (Right_Opnd (Expr),
                                                      Base,
                                                      Domain,
                                                      Local_Params)),
                                 Typ      => Base);
               end;

            else
               T := New_Op_Expr
                 (Op          => Nkind (Expr),
                  Right       =>
                    Transform_Expr (Right_Opnd (Expr),
                      EW_Bool_Type,
                      Domain,
                      Local_Params),
                  Right_Type  => Etype (Right_Opnd (Expr)),
                  Return_Type => Expr_Type,
                  Domain      => Domain,
                  Ada_Node    => Expr);
            end if;

         when N_Op_And | N_Op_Or | N_Op_Xor =>

            if Is_Array_Type (Etype (Left_Opnd (Expr))) then
               declare
                  Subdomain : constant EW_Domain :=
                    (if Domain = EW_Pred then EW_Term else Domain);
               begin

                  T := New_Op_Expr
                    (Op          => Nkind (Expr),
                     Left        =>
                       Transform_Expr (Left_Opnd (Expr), Subdomain, Params),
                     Right       =>
                       Transform_Expr (Right_Opnd (Expr), Subdomain, Params),
                     Left_Type   => Etype (Left_Opnd (Expr)),
                     Right_Type  => Etype (Right_Opnd (Expr)),
                     Return_Type => Expr_Type,
                     Domain      => Domain,
                     Ada_Node    => Expr);
               end;
            else
               declare
                  Base  : constant W_Type_Id :=
                    (if Is_Boolean_Type (Expr_Type) then EW_Bool_Type
                     else Base_Why_Type (Expr_Type));
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

                  T := New_Op_Expr
                    (Op          => Nkind (Expr),
                     Left        => Left,
                     Right       => Right,
                     Left_Type   => Etype (Left_Opnd (Expr)),
                     Right_Type  => Etype (Right_Opnd (Expr)),
                     Return_Type => Expr_Type,
                     Domain      => Domain,
                     Ada_Node    => Expr);
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

            --  Start of processing for Short_Circuit

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
            T := Transform_Concatenation
              (Left               =>
                  Transform_Expr (Left_Opnd (Expr), Domain, Params),
               Right              =>
                  Transform_Expr (Right_Opnd (Expr), Domain, Params),
               Left_Type          => Etype (Left_Opnd (Expr)),
               Right_Type         => Etype (Right_Opnd (Expr)),
               Return_Type        => Etype (Expr),
               Is_Component_Left  => Is_Component_Left_Opnd (Expr),
               Is_Component_Right => Is_Component_Right_Opnd (Expr),
               Domain             => Domain,
               Ada_Node           => Expr);

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
                                              Expected_Type,
                                              Domain,
                                              Local_Params);
               Else_Expr :=
                 Transform_Expr_With_Actions (Else_Part,
                                              Else_Actions (Expr),
                                              Expected_Type,
                                              Domain,
                                              Local_Params);
               Local_Params.Gen_Marker := False;
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

            --  When converting between elementary types, only require that the
            --  converted expression is translated into a value of the expected
            --  base type. Necessary checks, rounding and conversions will
            --  be introduced at the end of Transform_Expr below. Fixed-point
            --  types are special, because the base type __fixed really
            --  represents a different base for every fixed-point type, so
            --  use full conversion to the expected type in that case.

            if Is_Elementary_Type (Expr_Type)
              and not Has_Fixed_Point_Type (Expr_Type)
            then
               T := Transform_Expr (Expression (Expr),
                                    Base_Why_Type (Expr_Type),
                                    Domain,
                                    Local_Params);

            --  In other cases, require that the converted expression
            --  is translated into a value of the type of the conversion.

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
            if Is_Simple_Shift_Or_Rotate (Get_Called_Entity (Expr)) then
               T := Transform_Shift_Or_Rotate_Call
                      (Expr, Domain, Local_Params);
            else
               T := Transform_Function_Call (Expr, Domain, Local_Params);
            end if;

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
            Label_Set.Include (New_Located_Label (Expr, Left_Most => True));
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

         elsif Is_Floating_Point_Type (Expr_Type) then
            declare
               Tlo : constant Node_Id := Type_Low_Bound  (Expr_Type);
               Thi : constant Node_Id := Type_High_Bound (Expr_Type);
               Lov : Ureal;
               Hiv : Ureal;
               Lo  : Ureal;
               Hi  : Ureal;
               OK  : Boolean;
               True_Check_Inserted : Boolean := False;

            begin
              --  We can only remove the check if we can compute the expected
              --  bounds of the Range_Type now.

               if Compile_Time_Known_Value (Tlo)
                 and then Compile_Time_Known_Value (Thi)
               then
                  Lov := Expr_Value_R (Tlo);
                  Hiv := Expr_Value_R (Thi);

                  Determine_Range_R
                    (Expr, OK, Lo, Hi, Assume_Valid => True);

                  if OK then

                     --  If definitely in range, generate a check always true
                     --  for the overflow check. When gnat2why directly handles
                     --  check messages, a message could be generated instead
                     --  here.

                     --  Note in the test below that we assume that the range
                     --  is not OK if a bound of the range is equal to that
                     --  of the type. That's not the most precise check, but
                     --  we do it for the same reasons as those presented in
                     --  Checks.Enable_Overflow_Check in the same case.

                     if Lo > Lov and then Hi < Hiv then
                        True_Check_Inserted := True;
                        Emit_Always_True_Range_Check (Expr, RCK_Overflow);
                     end if;
                  end if;
               end if;

               if not True_Check_Inserted then
                  T := Insert_Overflow_Check (Expr, T, Expr_Type);
               end if;
            end;

         --  Not a signed integer type or a floating-point type. Always perform
         --  the overflow check.

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

   -----------------------------
   -- Transform_Function_Call --
   -----------------------------

   function Transform_Function_Call
     (Expr     : Node_Id;
      Domain   : EW_Domain;
      Params   : Transformation_Params) return W_Expr_Id
   is
      Nb_Of_Refs : Natural;
      Nb_Of_Lets : Natural;
      T          : W_Expr_Id;
      Subp       : constant Entity_Id := Get_Called_Entity (Expr);

      Args       : constant W_Expr_Array :=
        Compute_Call_Args (Expr, Domain, Nb_Of_Refs, Nb_Of_Lets, Params);

      Selector   : constant Selection_Kind :=
         --  When the call is dispatching, use the Dispatch variant of
         --  the program function, which has the appropriate contract.

        (if Present (Controlling_Argument (Expr)) then Dispatch

         --  When the call has visibility over the refined postcondition of the
         --  subprogram, use the Refine variant of the program function, which
         --  has the appropriate refined contract.

         elsif Has_Contracts (Subp, Name_Refined_Post)
           and then Has_Visibility_On_Refined (Expr, Subp)
         then
            Refine

         --  Otherwise use the Standard variant of the program function
         --  (defined outside any namespace, directly in the module for
         --  the program function).

         else Why.Inter.Standard);

      Why_Name   : constant W_Identifier_Id :=
        W_Identifier_Id
          (Transform_Identifier (Params   => Params,
                                 Expr     => Expr,
                                 Ent      => Subp,
                                 Domain   => Domain,
                                 Selector => Selector));

   begin
      if Why_Subp_Has_Precondition (Subp, Selector) then
         T := +New_VC_Call
           (Ada_Node => Expr,
            Name     => Why_Name,
            Progs    => Args,
            Reason   => VC_Precondition,
            Domain   => Domain,
            Typ      => Get_Typ (Why_Name));
      else
         T := New_Call
           (Name     => Why_Name,
            Args     => Args,
            Ada_Node => Expr,
            Domain   => Domain,
            Typ      => Get_Typ (Why_Name));
      end if;

      if Domain = EW_Prog then
         if Present (Controlling_Argument (Expr)) then
            T := +Sequence (Compute_Tag_Check (Expr, Params),
                            +T);
         end if;
      end if;

      --  SPARK function cannot have side-effects
      pragma Assert (Nb_Of_Refs = 0);

      return T;
   end Transform_Function_Call;

   --------------------------
   -- Transform_Identifier --
   --------------------------

   function Transform_Identifier
     (Params   : Transformation_Params;
      Expr     : Node_Id;
      Ent      : Entity_Id;
      Domain   : EW_Domain;
      Selector : Selection_Kind := Why.Inter.Standard) return W_Expr_Id
   is
      C        : constant Ada_Ent_To_Why.Cursor :=
        Ada_Ent_To_Why.Find (Symbol_Table, Ent);
      T        : W_Expr_Id;
      Is_Deref : Boolean := False;
   begin
      --  The special cases of this function are:
      --  * parameters, whose names are stored in Params.Name_Map (these can
      --    also be refs)
      --  * enumeration literals (we have a separate function)
      --  * ids of Standard.ASCII (transform to integer)
      --  * quantified variables (use local name instead of global name)
      --  * fields of protected objects

      if Ada_Ent_To_Why.Has_Element (C) then
         declare
            E : constant Item_Type := Ada_Ent_To_Why.Element (C);
         begin
            --  If E is a function and Domain is Prog, use the program specific
            --  identifier instead.

            case E.Kind is
               when Func =>
                  if Domain = EW_Prog then
                     T := +E.For_Prog.B_Name;
                  else
                     T := +E.For_Logic.B_Name;
                  end if;
               when Regular | Prot_Self =>
                  T := +E.Main.B_Name;
               when UCArray =>
                  T := +E.Content.B_Name;
               when DRecord =>

                  T := Record_From_Split_Form (E, Params.Ref_Allowed);
                  Is_Deref := True;

                  --  Havoc the references of Ent for volatiles with
                  --  Async_Writers.

                  if Has_Async_Writers (Direct_Mapping_Id (Ent))
                    and then Domain = EW_Prog
                  then
                     pragma Assert (Is_Mutable_In_Why (Ent));
                     pragma Assert (Params.Ref_Allowed);

                     --  Assume dynamic invariant of the object after havoc.

                     declare
                        Dyn_Prop : constant W_Pred_Id :=
                          Compute_Dynamic_Invariant (Expr   => +T,
                                                     Ty     => E.Typ,
                                                     Params => Params);
                     begin
                        if Dyn_Prop /= True_Pred then
                           T := +Sequence
                             (New_Assume_Statement (Pred => Dyn_Prop),
                              +T);
                        end if;
                     end;

                     --  Havoc the reference for fields

                     if E.Fields.Present then
                        pragma Assert (E.Fields.Binder.Mutable);

                        T := +Sequence
                          (New_Havoc_Call (E.Fields.Binder.B_Name),
                           +T);
                     end if;

                     --  If the object is not constrained then also havoc the
                     --  reference for discriminants

                     if E.Discrs.Present and then E.Discrs.Binder.Mutable then
                        pragma Assert (E.Constr.Present);

                        declare
                           Havoc_Discr      : constant W_Prog_Id :=
                             New_Havoc_Call (E.Discrs.Binder.B_Name);
                           Havoc_Discr_Cond : constant W_Expr_Id :=
                             New_Conditional
                               (Domain      => EW_Prog,
                                Condition   => New_Not
                                  (Domain   => EW_Prog,
                                   Right    => +E.Constr.Id),
                                Then_Part   => +Havoc_Discr);
                        begin
                           T := +Sequence  (+Havoc_Discr_Cond, +T);
                        end;
                     end if;
                  end if;
            end case;

            --  ??? no use of T below when test succeeds? (except for its type)

            if Selector /= Why.Inter.Standard then
               T := +To_Why_Id (Ent, Domain,
                                Selector => Selector,
                                Typ      => Get_Type (T));
            end if;
         end;
      elsif Ekind (Ent) = E_Enumeration_Literal then
         T := Transform_Enum_Literal (Expr, Ent, Domain);

      elsif Sloc (Ent) = Standard_ASCII_Location then
         T :=
           New_Integer_Constant
             (Value => Char_Literal_Value (Constant_Value (Ent)));
      elsif Is_Protected_Component_Or_Discr (Ent)
        or else Is_Part_Of_Protected_Object (Ent)
      then
         declare
            Obj_Or_Ty : constant Entity_Id :=
              Get_Enclosing_Concurrent_Object (Ent);
            Prot : constant Entity_Id :=
              (if Is_Type (Obj_Or_Ty) then Obj_Or_Ty else Etype (Obj_Or_Ty));
            Id   : constant W_Identifier_Id :=
              New_Identifier
                (Name => "self__",
                 Typ  => Type_Of_Node (Prot));
         begin
            T := New_Ada_Record_Access
              (Ada_Node => Expr,
               Domain   => Domain,
               Name     =>
                 (if Self_Is_Mutable
                  then New_Deref (Right => Id, Typ => Type_Of_Node (Prot))
                    else +Id),
               Field    => Ent,
               Ty       => Prot);
         end;
      else
         Ada.Text_IO.Put_Line ("[Transform_Identifier] unregistered entity "
                               & Full_Name (Ent));
         raise Program_Error;
      end if;

      --  If we have an object with Async_Writers, we must havoc it before
      --  dereferencing it. Given a ref term t, this produces the sequence:
      --     (__havoc(t); !t)
      --  It is sound (and necessary) to only do that in the program domain. We
      --  can be sure that the relevant Ada code will pass this point at least
      --  once in program domain.

      if Has_Async_Writers (Direct_Mapping_Id (Ent))
        and then Domain = EW_Prog
        and then not Is_Deref
        and then not Is_Part_Of_Protected_Object (Ent)
      then
         pragma Assert (Is_Mutable_In_Why (Ent));
         pragma Assert (Params.Ref_Allowed);

         declare
            Deref    : constant W_Expr_Id :=
              New_Deref (Ada_Node => Get_Ada_Node (+T),
                         Right    => +T,
                         Typ      => Get_Type (T));
            Dyn_Prop : constant W_Pred_Id :=
              Compute_Dynamic_Invariant (Expr   => +Deref,
                                        Ty     => Etype (Ent),
                                        Params => Params);
            Havoc    : W_Prog_Id := New_Havoc_Call (+T);
         begin
            if Dyn_Prop /= True_Pred then

               --  Assume dynamic invariant of the object after the havoc.

               Havoc := +Sequence
                 (Havoc, New_Assume_Statement (Pred => Dyn_Prop));
            end if;

            T := +Sequence (Left  => Havoc,
                            Right => +Deref);
         end;

      elsif Is_Mutable_In_Why (Ent)
        and then Params.Ref_Allowed
        and then not Is_Deref
      then
         T := New_Deref (Ada_Node => Get_Ada_Node (+T),
                         Right    => +T,
                         Typ      => Get_Type (T));
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
        (Var       : W_Expr_Id;
         Alt       : Node_Id;
         Base_Type : W_Type_Id)
         return W_Expr_Id;
      --  If the alternative Alt is a subtype mark, transform it as a simple
      --  membership test "Var in Alt". Otherwise transform it as an equality
      --  test "Var = Alt".

      function Transform_Simple_Membership_Expression
        (Var     : W_Expr_Id;
         In_Expr : Node_Id) return W_Expr_Id;

      ---------------------------
      -- Transform_Alternative --
      ---------------------------

      function Transform_Alternative
        (Var       : W_Expr_Id;
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
              (Symbol => Why_Eq,
               Left   => Var,
               Right  => Transform_Expr (Expr          => Alt,
                                         Expected_Type => Base_Type,
                                         Domain        => EW_Term,
                                         Params        => Params),
               Domain => Domain);
         end if;

         return Result;
      end Transform_Alternative;

      --------------------------------------------
      -- Transform_Simple_Membership_Expression --
      --------------------------------------------

      function Transform_Simple_Membership_Expression
        (Var     : W_Expr_Id;
         In_Expr : Node_Id) return W_Expr_Id
      is
         True_Expr : constant W_Expr_Id :=
           (if Domain = EW_Pred then +True_Pred else +True_Term);
         Result    : W_Expr_Id;

      begin
         --  First handle the simpler case of s subtype mark
         --  Classwide types appear as a N_Attribute_Reference.

         if (Nkind (In_Expr) in N_Identifier | N_Expanded_Name
             and then Is_Type (Entity (In_Expr)))
           or else (Nkind (In_Expr) = N_Attribute_Reference
                    and then Get_Attribute_Id (Attribute_Name (In_Expr)) =
                      Attribute_Class)
         then
            declare
               Ty : constant Entity_Id := Unique_Entity (Entity (In_Expr));

            begin
               --  Record subtypes are special

               if Is_Record_Type (Ty) then

                  --  We must check for two cases. Ty may be constrained, in
                  --  which case we need to check its dicriminant, or it may
                  --  be tagged, in which case we need to check its tag.

                  declare
                     Discr_Cond : W_Expr_Id := True_Expr;
                     Tag_Cond   : W_Expr_Id := True_Expr;
                     Spec_Ty    : constant Entity_Id :=
                       (if Is_Class_Wide_Type (Ty)
                        then Retysp (Get_Specific_Type_From_Classwide (Ty))
                        else Ty);
                  begin

                     --  If Ty is constrained, we need to check its
                     --  discriminant.
                     --  It is also the case if Ty's specific type is
                     --  constrained, see RM 3.9 (14)

                     if Root_Type (Spec_Ty) /= Spec_Ty and then
                       Has_Discriminants (Spec_Ty) and then
                       Is_Constrained (Spec_Ty)
                     then
                        Discr_Cond := New_Call
                          (Domain => Domain,
                           Name => E_Symb (Spec_Ty, WNE_Range_Pred),
                           Args =>
                             Prepare_Args_For_Subtype_Check (Spec_Ty, Var),
                           Typ  => EW_Bool_Type);
                     end if;

                     --  If Ty is tagged, we need to check its tag.

                     if Is_Tagged_Type (Ty)
                       and then Is_Class_Wide_Type (Ty)
                     then

                        --  If we are checking against a classwide type, it is
                        --  enough to check wether Var can be converted to Ty.

                        declare
                           Var_Type : constant Entity_Id :=
                             Get_Ada_Node (+Get_Type (Var));
                        begin
                           pragma Assert (Present (Var_Type));

                           if not SPARK_Util.Is_Ancestor (Ty, Var_Type) then
                              Tag_Cond := New_Call
                                (Domain => Domain,
                                 Name => M_Main.Compat_Tags_Id,
                                 Args => (1 => New_Tag_Access
                                          (Domain   => EW_Term,
                                           Name     => Var,
                                           Ty       => Var_Type),
                                          2 => +E_Symb (E => Ty,
                                                        S => WNE_Tag)),
                                 Typ  => EW_Bool_Type);
                           end if;
                        end;
                     elsif Is_Tagged_Type (Ty) then

                        --  If we are checking against a specific type, then
                        --  the tags of Var and Ty must match.

                        Tag_Cond := New_Call
                          (Domain => Domain,
                           Name => Why_Eq,
                           Args => (1 => New_Tag_Access
                                    (Domain   => EW_Term,
                                     Name     => Var,
                                     Ty       =>
                                       Get_Ada_Node (+Get_Type (Var))),
                                    2 => +E_Symb (E => Ty,
                                                  S => WNE_Tag)),
                           Typ  => EW_Bool_Type);
                     end if;

                     --  Go back to the appropriate domain

                     declare
                        Condition : constant W_Expr_Id :=
                          New_And_Expr (Discr_Cond, Tag_Cond, Domain);
                     begin
                        if Domain = EW_Pred then
                           Result := Condition;
                        else
                           Result :=
                             New_Conditional
                               (Domain    => Domain,
                                Condition => Condition,
                                Then_Part => True_Expr,
                                Else_Part =>
                                  New_Literal (Domain => EW_Term,
                                               Value => EW_False),
                                Typ       => EW_Bool_Type);
                        end if;
                     end;
                  end;
               else
                  pragma Assert (Is_Scalar_Type (Ty));
                  if Type_Is_Modeled_As_Base (Ty) then
                     Result := New_Dynamic_Property (Domain => Domain,
                                                     Ty     => Ty,
                                                     Expr   => Var);
                  else
                     declare
                        Name : constant W_Identifier_Id :=
                          (if Is_Standard_Boolean_Type (Ty) then
                                M_Boolean.Range_Pred
                           else E_Symb (Ty, WNE_Range_Pred));
                     begin
                        Result :=
                          New_Call (Domain => Domain,
                                    Name => Name,
                                    Args => (1 => Var),
                                    Typ  => EW_Bool_Type);
                     end;
                  end if;
               end if;

               --  Possibly include a predicate in the type membership
               --  test. A temporary needs to be introduced if Var is not
               --  a simple variable, so that we can always pass a term to
               --  Compute_Dynamic_Predicate, even when Domain = EW_Prog.
               --  This is needed because the pred expression returned by
               --  Compute_Dynamic_Predicate may then be converted back to a
               --  Why3 prog expression by Boolean_Expr_Of_Pred, which requires
               --  its argument to be a pred expression.

               if Has_Predicates (Ty) then
                  declare
                     Tmp : constant W_Expr_Id := New_Temp_For_Expr (Var);
                  begin
                     Result := New_And_Expr
                       (Result,
                        Boolean_Expr_Of_Pred
                          (Compute_Dynamic_Predicate (+Tmp, Ty, Params),
                           Domain),
                        Domain);
                     Result := Binding_For_Temp (Domain  => Domain,
                                                 Tmp     => Tmp,
                                                 Context => Result);
                  end;
               end if;
            end;
         else
            Result := Range_Expr (In_Expr, Var, Domain, Params);
         end if;

         return Result;
      end Transform_Simple_Membership_Expression;

      Var       : constant Node_Id := Left_Opnd (Expr);
      Result    : W_Expr_Id;
      Base_Type : W_Type_Id :=
        (if Has_Record_Type (Etype (Var)) then
            EW_Abstract (Root_Record_Type (Etype (Var)))
         else Base_Why_Type (Var));
      --  For records, checks are done on the root type.

      Subdomain : constant EW_Domain :=
        (if Domain = EW_Pred then EW_Term else Domain);
      Var_Expr  : W_Expr_Id;

   --  Start of processing for Transform_Membership_Expression

   begin
      --  For ranges and membership, "bool" should be mapped to "int".

      if Base_Type = EW_Bool_Type then
         Base_Type := EW_Int_Type;
      end if;
      Var_Expr := Transform_Expr (Var, Base_Type, Subdomain, Params);

      if Present (Alternatives (Expr)) then
         declare
            Alt : Node_Id;
         begin
            Var_Expr := New_Temp_For_Expr (Var_Expr, True);
            Alt := Last (Alternatives (Expr));
            Result := Transform_Alternative (Var_Expr, Alt, Base_Type);

            Prev (Alt);
            while Present (Alt) loop
               Result := New_Or_Else_Expr
                 (Left   => Transform_Alternative (Var_Expr, Alt, Base_Type),
                  Right  => Result,
                  Domain => Domain);
               Prev (Alt);
            end loop;
            Result := Binding_For_Temp (Domain  => Domain,
                                        Tmp     => Var_Expr,
                                        Context => Result);
         end;
      else
         Result :=
           Transform_Simple_Membership_Expression
             (Var_Expr, Right_Opnd (Expr));
      end if;

      --  Inverse the result if the operator is NOT IN

      if Nkind (Expr) = N_Not_In then
         if Domain = EW_Term then
            Result := New_Call
              (Ada_Node => Expr,
               Domain   => Domain,
               Name     => M_Boolean.Notb,
               Args     => (1 => Result),
               Typ      => EW_Bool_Type);

         else
            Result := New_Not (Right  => Result, Domain => Domain);
         end if;
      end if;

      return Result;
   end Transform_Membership_Expression;

   ----------------------------------------------
   -- Transform_Non_Standard_Modulus_Operation --
   ----------------------------------------------

   function Transform_Non_Binary_Modular_Operation
     (Ada_Node   : Node_Id;
      Ada_Type   : Entity_Id;
      Domain     : EW_Domain;
      Op         : N_Op;
      Left_Opnd  : W_Expr_Id := Why_Empty;
      Right_Opnd : W_Expr_Id;
      Rep_Type   : W_Type_Id;
      Modulus    : Uint) return W_Expr_Id
   is
      T : W_Expr_Id;

   begin
      --  GNAT only supports non binary modulus up to 2**32. We use this
      --  limitation here to simplify the implementation, so we check this
      --  is the case here.

      if Modulus >= UI_Expon (2, 32) then
         raise Program_Error;
      end if;

      case Op is

         --  Transform (-Y) into:
         --    (Modulus - Y) modulo Modulus
         --  We add the extra modulo in order to deal with the special case
         --  of -0. We use modulo instead of a test in order to have a fully
         --  computational interpretation.

         when N_Op_Minus =>
            pragma Assert (Left_Opnd = Why_Empty);

            declare
               Modulus_Expr : constant W_Expr_Id :=
                 New_Modular_Constant
                   (Value => Modulus,
                    Typ   => Rep_Type);
               Sub : constant W_Expr_Id :=
                 New_Call
                   (Ada_Node => Ada_Node,
                    Domain   => Domain,
                    Name     => MF_BVs (Rep_Type).Sub,
                    Args     =>
                      (1 => Modulus_Expr,
                       2 => Right_Opnd),
                    Typ      => Rep_Type);
            begin
               T :=  New_Call (Domain => Domain,
                               Name   => MF_BVs (Rep_Type).Urem,
                               Args   =>
                                 (1 => Sub,
                                  2 => Modulus_Expr),
                               Typ    => Rep_Type);
            end;

         --  Transform (X + Y) into:
         --    if Modulus - X <= Y
         --    then (X + Y) - Modulus
         --    else X + Y

         when N_Op_Add =>
            declare
               BV            : constant M_BV_Type := MF_BVs (Rep_Type);
               Modulus_Expr : constant W_Expr_Id :=
                 New_Modular_Constant (Value => Modulus,
                                       Typ   => Rep_Type);
               Add_Expr      : constant W_Expr_Id :=
                 New_Call (Ada_Node => Ada_Node,
                           Domain   => Domain,
                           Name     => BV.Add,
                           Args     => (1 => Left_Opnd,
                                        2 => Right_Opnd),
                           Typ   => Rep_Type);
               Add_Id        : constant W_Expr_Id :=
                 New_Temp_For_Expr (E => Add_Expr);
               Overflow_Test : constant W_Expr_Id :=
                 New_Call (Domain => Domain,
                           Name   => BV.Ule,
                           Args   =>
                             (1 => New_Call (Domain => Domain,
                                             Name   => BV.Sub,
                                             Args   => (1 => Modulus_Expr,
                                                        2 => Left_Opnd),
                                             Typ    => Rep_Type),
                              2 => Right_Opnd),
                           Typ    => EW_Bool_Type);
               Modulo_Expr   : constant W_Expr_Id :=
                 New_Call (Ada_Node => Ada_Node,
                           Domain   => Domain,
                           Name     => BV.Sub,
                           Args     => (1 => Add_Id,
                                        2 => Modulus_Expr),
                           Typ      => Rep_Type);
               Ite_Expr      : constant W_Conditional_Id :=
                 New_Conditional (Ada_Node    => Ada_Node,
                                  Domain      => Domain,
                                  Condition   => Overflow_Test,
                                  Then_Part   => Modulo_Expr,
                                  Else_Part   => Add_Id,
                                  Typ         => Rep_Type);
            begin
               T := Binding_For_Temp (Ada_Node => Ada_Node,
                                      Domain   => Domain,
                                      Tmp      => Add_Id,
                                      Context  => +Ite_Expr);
            end;

         --  Transform (X - Y) into:
         --    if Y > X
         --    then (X - Y) + Modulus
         --    else X - Y

         when N_Op_Subtract =>
            declare
               BV            : constant M_BV_Type := MF_BVs (Rep_Type);
               Modulus_Expr : constant W_Expr_Id :=
                 New_Modular_Constant (Value => Modulus,
                                       Typ   => Rep_Type);
               Sub_Expr      : constant W_Expr_Id :=
                 New_Call (Ada_Node => Ada_Node,
                           Domain   => Domain,
                           Name     => BV.Sub,
                           Args     => (1 => Left_Opnd,
                                        2 => Right_Opnd),
                           Typ   => Rep_Type);
               Sub_Id        : constant W_Expr_Id :=
                 New_Temp_For_Expr (E => Sub_Expr);
               Overflow_Test  : constant W_Expr_Id :=
                 New_Call (Domain   => Domain,
                           Name     => BV.Ult,
                           Args     => (1 => Left_Opnd,
                                        2 => Right_Opnd),
                           Typ      => EW_Bool_Type);
               Modulo_Expr   : constant W_Expr_Id :=
                 New_Call (Ada_Node => Ada_Node,
                           Domain   => Domain,
                           Name     => BV.Add,
                           Args     => (1 => Sub_Id,
                                        2 => Modulus_Expr),
                           Typ      => Rep_Type);
               Ite_Expr      : constant W_Conditional_Id :=
                 New_Conditional (Ada_Node    => Ada_Node,
                                  Domain      => Domain,
                                  Condition   => Overflow_Test,
                                  Then_Part   => Modulo_Expr,
                                  Else_Part   => Sub_Id,
                                  Typ         => Rep_Type);
            begin
               T := Binding_For_Temp (Ada_Node => Ada_Node,
                                      Domain   => Domain,
                                      Tmp      => Sub_Id,
                                      Context  => +Ite_Expr);
            end;

         --  In those cases where the multiplication may not fit in the size of
         --  bitvector of [Rep_Type], convert both operands to the next size of
         --  bitvector, do the multiplication without overflow in that larger
         --  type, then apply the modulus and convert back to the original
         --  type.

         when N_Op_Multiply =>
            declare
               Next_Bv    : constant W_Type_Id :=
                 (if Modulus < UI_Expon (2, 8) then
                    (if Esize (Ada_Type) < 16 then EW_BitVector_16_Type
                     else Rep_Type)
                  elsif Modulus < UI_Expon (2, 16) then
                     (if Esize (Ada_Type) < 32 then EW_BitVector_32_Type
                     else Rep_Type)
                  else
                     EW_BitVector_64_Type);
               Modulus_Expr : constant W_Expr_Id :=
                 New_Modular_Constant (Value => Modulus,
                                       Typ   => Next_Bv);
               Next_Left  : constant W_Expr_Id :=
                 Insert_Simple_Conversion (Domain => Domain,
                                           Expr   => Left_Opnd,
                                           To     => Next_Bv);
               Next_Right : constant W_Expr_Id :=
                 Insert_Simple_Conversion (Domain => Domain,
                                           Expr   => Right_Opnd,
                                           To     => Next_Bv);
               Mul_Expr   : constant W_Expr_Id :=
                 New_Call (Ada_Node => Ada_Node,
                           Domain   => Domain,
                           Name     => MF_BVs (Next_Bv).Mult,
                           Args     => (1 => Next_Left,
                                        2 => Next_Right),
                           Typ      => Next_Bv);
               Modulo_Expr : constant W_Expr_Id :=
                 New_Call (Name   => MF_BVs (Next_Bv).Urem,
                           Domain => Domain,
                           Args   => (1 => Mul_Expr,
                                      2 => Modulus_Expr),
                           Typ    => Next_Bv);
            begin
               T := Insert_Simple_Conversion (Ada_Node => Ada_Node,
                                              Domain   => Domain,
                                              Expr     => Modulo_Expr,
                                              To       => Rep_Type);
            end;

         when others =>
            raise Program_Error;
      end case;

      return T;
   end Transform_Non_Binary_Modular_Operation;

   ----------------------
   -- Transform_Pragma --
   ----------------------

   function Transform_Pragma
     (Prag  : Node_Id;
      Force : Boolean) return W_Prog_Id
   is
      Pname   : constant Name_Id   := Pragma_Name (Prag);
      Prag_Id : constant Pragma_Id := Get_Pragma_Id (Pname);

      procedure tip;
      --  A dummy procedure called when pragma Inspection_Point is processed.
      --  This is just to help debugging Why generation. If a pragma
      --  Inspection_Point is added to a source program, then breaking on
      --  tip will get you to that point in the program.

      ---------
      -- tip --
      ---------

      procedure tip is
      begin
         null;
      end tip;

   --  Start of processing for Transform_Pragma

   begin
      case Prag_Id is

         --  Ignore pragma Check for preconditions and postconditions

         when Pragma_Check =>
            return Transform_Pragma_Check (Prag, Force);

         --  Pragma Overflow_Mode should have an effect on proof, but is
         --  currently ignored (and a corresponding warning is issued
         --  during marking).

         when Pragma_Overflow_Mode =>
            return New_Void (Prag);

         --  Unless Force is True to force the translation of pragmas
         --  Precondition and Postcondition (for those pragmas declared in
         --  a subprogram body), these pragmas are translated elsewhere.

         when Pragma_Precondition | Pragma_Postcondition =>
            if Force then
               declare
                  Expr   : constant Node_Id :=
                    Expression (First (Pragma_Argument_Associations (Prag)));
                  Params : Transformation_Params := Assert_Params;
                  Result : W_Prog_Id;

               begin
                  Result := New_Ignore
                    (Prog =>
                       +Transform_Expr (Expr, EW_Prog, Params => Params));
                  Params.Gen_Marker := True;
                  Result := Sequence
                    (Result,
                     New_Located_Assert
                       (Prag,
                        +Transform_Expr (Expr, EW_Pred, Params => Params),
                        VC_Assert,
                        EW_Assert));
                  return Result;
               end;
            else
               return New_Void (Prag);
            end if;

         --  Pragma Inspection_Point is ignored, but we insert a call to a
         --  dummy procedure, to allow to break on it during debugging.

         when Pragma_Inspection_Point =>
            tip;
            return New_Void (Prag);

         --  Do not issue a warning on invariant pragmas, as one is already
         --  issued on the corresponding type in SPARK.Definition.

         when Pragma_Invariant
            | Pragma_Type_Invariant
            | Pragma_Type_Invariant_Class =>
            return New_Void (Prag);

         --  ??? Currently ignored, see NA03-001

         when Pragma_Extensions_Visible =>
            return New_Void (Prag);

         --  Do not issue a warning on unknown pragmas, as one is already
         --  issued in SPARK.Definition.

         when Unknown_Pragma =>
            return New_Void (Prag);

         --  Remaining pragmas fall into two major groups:
         --
         --  Group 1 - ignored
         --
         --  Pragmas that do not need any marking, either because:
         --  . they are defined by SPARK 2014, or
         --  . they are already taken into account elsewhere (contracts)
         --  . they have no effect on verification

         --  Group 1a - RM Table 16.1, Ada language-defined pragmas marked
         --  "Yes".
         --  Note: pragma Assert is transformed into an
         --  instance of pragma Check by the front-end.
         when Pragma_Assertion_Policy             |
              Pragma_Atomic                       |
              Pragma_Atomic_Components            |
              Pragma_Convention                   |
              Pragma_Elaborate                    |
              Pragma_Elaborate_All                |
              Pragma_Elaborate_Body               |
              Pragma_Export                       |
              Pragma_Import                       |
              Pragma_Independent                  |
              Pragma_Independent_Components       |
              Pragma_Inline                       |
              Pragma_Linker_Options               |
              Pragma_List                         |
              Pragma_No_Return                    |
              Pragma_Normalize_Scalars            |
              Pragma_Optimize                     |
              Pragma_Pack                         |
              Pragma_Page                         |
              Pragma_Partition_Elaboration_Policy |
              Pragma_Preelaborable_Initialization |
              Pragma_Preelaborate                 |
              Pragma_Profile                      |
              Pragma_Pure                         |
              Pragma_Restrictions                 |
              Pragma_Reviewable                   |
              Pragma_Suppress                     |
              Pragma_Unsuppress                   |
              Pragma_Volatile                     |
              Pragma_Volatile_Components          |
              Pragma_Volatile_Full_Access         |

         --  Group 1b - RM Table 16.2, SPARK language-defined pragmas marked
         --  "Yes", whose effect on proof is taken care of somewhere else.
         --  Note: pragmas Assert_And_Cut, Assume, and
         --  Loop_Invariant are transformed into instances of
         --  pragma Check by the front-end.
              Pragma_Abstract_State               |
              Pragma_Assume_No_Invalid_Values     |
              Pragma_Async_Readers                |
              Pragma_Async_Writers                |
              Pragma_Constant_After_Elaboration   |
              Pragma_Contract_Cases               |
              Pragma_Depends                      |
              Pragma_Default_Initial_Condition    |
              Pragma_Effective_Reads              |
              Pragma_Effective_Writes             |
              Pragma_Ghost                        |
              Pragma_Global                       |
              Pragma_Initializes                  |
              Pragma_Initial_Condition            |
              Pragma_Loop_Variant                 |
              Pragma_Part_Of                      |
              Pragma_Refined_Depends              |
              Pragma_Refined_Global               |
              Pragma_Refined_Post                 |
              Pragma_Refined_State                |
              Pragma_SPARK_Mode                   |
              Pragma_Unevaluated_Use_Of_Old       |
              Pragma_Volatile_Function            |

         --  Group 1c - RM Table 16.3, GNAT implementation-defined pragmas
         --  marked "Yes".
         --  Note: pragma Debug is removed by the front-end.
              Pragma_Ada_83                       |
              Pragma_Ada_95                       |
              Pragma_Ada_05                       |
              Pragma_Ada_2005                     |
              Pragma_Ada_12                       |
              Pragma_Ada_2012                     |
              Pragma_Annotate                     |
              Pragma_Check_Policy                 |
              Pragma_Ignore_Pragma                |
              Pragma_Inline_Always                |
              Pragma_Linker_Section               |
              Pragma_No_Elaboration_Code_All      |
              Pragma_No_Tagged_Streams            |
              Pragma_Pure_Function                |
              Pragma_Restriction_Warnings         |
              Pragma_Style_Checks                 |
              Pragma_Test_Case                    |
              Pragma_Unmodified                   |
              Pragma_Unreferenced                 |
              Pragma_Validity_Checks              |
              Pragma_Warnings                     |
              Pragma_Weak_External                =>
            return New_Void (Prag);

         --  Group 1d - pragma that are re-written and/or removed
         --  by the front-end in GNATprove, so they should
         --  never be seen here.
         when Pragma_Assert                       |
              Pragma_Assert_And_Cut               |
              Pragma_Assume                       |
              Pragma_Debug                        |
              Pragma_Loop_Invariant               =>
            raise Program_Error;

         --  Group 2 - Remaining pragmas, enumerated here rather than
         --  a "when others" to force re-consideration when
         --  SNames.Pragma_Id is extended.
         --
         --  These all generate a warning.  In future, these pragmas
         --  may move to be fully ignored or to be processed with more
         --  semantic detail as required.

         --  Group 2a - GNAT Defined and obsolete pragmas
         when Pragma_Abort_Defer                 |
           Pragma_Allow_Integer_Address          |
           Pragma_Attribute_Definition           |
           Pragma_C_Pass_By_Copy                 |
           Pragma_Check_Float_Overflow           |
           Pragma_Check_Name                     |
           Pragma_Comment                        |
           Pragma_Common_Object                  |
           Pragma_Compile_Time_Error             |
           Pragma_Compile_Time_Warning           |
           Pragma_Compiler_Unit                  |
           Pragma_Compiler_Unit_Warning          |
           Pragma_Complete_Representation        |
           Pragma_Complex_Representation         |
           Pragma_Component_Alignment            |
           Pragma_Controlled                     |
           Pragma_Convention_Identifier          |
           Pragma_CPP_Class                      |
           Pragma_CPP_Constructor                |
           Pragma_CPP_Virtual                    |
           Pragma_CPP_Vtable                     |
           Pragma_CPU                            |
           Pragma_Debug_Policy                   |
           Pragma_Default_Scalar_Storage_Order   |
           Pragma_Default_Storage_Pool           |
           Pragma_Detect_Blocking                |
           Pragma_Disable_Atomic_Synchronization |
           Pragma_Dispatching_Domain             |
           Pragma_Elaboration_Checks             |
           Pragma_Eliminate                      |
           Pragma_Enable_Atomic_Synchronization  |
           Pragma_Export_Function                |
           Pragma_Export_Object                  |
           Pragma_Export_Procedure               |
           Pragma_Export_Value                   |
           Pragma_Export_Valued_Procedure        |
           Pragma_Extend_System                  |
           Pragma_Extensions_Allowed             |
           Pragma_External                       |
           Pragma_External_Name_Casing           |
           Pragma_Fast_Math                      |
           Pragma_Favor_Top_Level                |
           Pragma_Finalize_Storage_Only          |
           Pragma_Ident                          |
           Pragma_Implementation_Defined         |
           Pragma_Implemented                    |
           Pragma_Implicit_Packing               |
           Pragma_Import_Function                |
           Pragma_Import_Object                  |
           Pragma_Import_Procedure               |
           Pragma_Import_Valued_Procedure        |
           Pragma_Initialize_Scalars             |
           Pragma_Inline_Generic                 |
           Pragma_Interface                      |
           Pragma_Interface_Name                 |
           Pragma_Interrupt_Handler              |
           Pragma_Interrupt_State                |
           Pragma_Keep_Names                     |
           Pragma_License                        |
           Pragma_Link_With                      |
           Pragma_Linker_Alias                   |
           Pragma_Linker_Constructor             |
           Pragma_Linker_Destructor              |
           Pragma_Loop_Optimize                  |
           Pragma_Machine_Attribute              |
           Pragma_Main                           |
           Pragma_Main_Storage                   |
           Pragma_Memory_Size                    |
           Pragma_No_Body                        |
           Pragma_No_Inline                      |
           Pragma_No_Run_Time                    |
           Pragma_No_Strict_Aliasing             |
           Pragma_Obsolescent                    |
           Pragma_Optimize_Alignment             |
           Pragma_Ordered                        |
           Pragma_Overriding_Renamings           |
           Pragma_Passive                        |
           Pragma_Persistent_BSS                 |
           Pragma_Polling                        |
           Pragma_Post                           |
           Pragma_Post_Class                     |
           Pragma_Pre                            |
           Pragma_Predicate                      |
           Pragma_Predicate_Failure              |
           Pragma_Prefix_Exception_Messages      |
           Pragma_Pre_Class                      |
           Pragma_Priority_Specific_Dispatching  |
           Pragma_Profile_Warnings               |
           Pragma_Propagate_Exceptions           |
           Pragma_Provide_Shift_Operators        |
           Pragma_Psect_Object                   |
           Pragma_Rational                       |
           Pragma_Ravenscar                      |
           Pragma_Relative_Deadline              |
           Pragma_Remote_Access_Type             |
           Pragma_Restricted_Run_Time            |
           Pragma_Share_Generic                  |
           Pragma_Shared                         |
           Pragma_Short_Circuit_And_Or           |
           Pragma_Short_Descriptors              |
           Pragma_Simple_Storage_Pool_Type       |
           Pragma_Source_File_Name               |
           Pragma_Source_File_Name_Project       |
           Pragma_Source_Reference               |
           Pragma_Static_Elaboration_Desired     |
           Pragma_Storage_Unit                   |
           Pragma_Stream_Convert                 |
           Pragma_Subtitle                       |
           Pragma_Suppress_All                   |
           Pragma_Suppress_Debug_Info            |
           Pragma_Suppress_Exception_Locations   |
           Pragma_Suppress_Initialization        |
           Pragma_System_Name                    |
           Pragma_Task_Info                      |
           Pragma_Task_Name                      |
           Pragma_Task_Storage                   |
           Pragma_Thread_Local_Storage           |
           Pragma_Time_Slice                     |
           Pragma_Title                          |
           Pragma_Unchecked_Union                |
           Pragma_Unimplemented_Unit             |
           Pragma_Universal_Aliasing             |
           Pragma_Universal_Data                 |
           Pragma_Unreferenced_Objects           |
           Pragma_Unreserve_All_Interrupts       |
           Pragma_Use_VADS_Size                  |
           Pragma_Warning_As_Error               |
           Pragma_Wide_Character_Encoding        |

           --  Group 2b - Ada RM pragmas
           Pragma_Discard_Names                  |
           Pragma_Locking_Policy                 |
           Pragma_Queuing_Policy                 |
           Pragma_Task_Dispatching_Policy        |
           Pragma_All_Calls_Remote               |
           Pragma_Asynchronous                   |
           Pragma_Attach_Handler                 |
           Pragma_Remote_Call_Interface          |
           Pragma_Remote_Types                   |
           Pragma_Shared_Passive                 |
           Pragma_Interrupt_Priority             |
           Pragma_Lock_Free                      |
           Pragma_Priority                       |
           Pragma_Storage_Size                   =>

            Error_Msg_Name_1 := Pragma_Name (Prag);
            Error_Msg_N
              ("?pragma % ignored in proof (not yet supported)", Prag);
            return New_Void (Prag);
      end case;
   end Transform_Pragma;

   ----------------------------
   -- Transform_Pragma_Check --
   ----------------------------

   procedure Transform_Pragma_Check
     (Stmt    :     Node_Id;
      Force   :     Boolean;
      Runtime : out W_Prog_Id;
      Pred    : out W_Pred_Id)
   is
      Arg1   : constant Node_Id := First (Pragma_Argument_Associations (Stmt));
      Arg2   : constant Node_Id := Next (Arg1);
      Expr   : constant Node_Id := Expression (Arg2);
      Params : Transformation_Params := Assert_Params;

   begin
      if not Force and then Is_Ignored_Pragma_Check (Stmt) then
         Runtime := New_Void (Stmt);
         Pred := True_Pred;
         return;
      end if;

      if Present (Expr) then
         Runtime := New_Ignore
           (Prog => +Transform_Expr (Expr, EW_Prog, Params => Params));
         Params.Gen_Marker := True;
         Pred := +Transform_Expr (Expr, EW_Pred, Params => Params);
         return;
      else
         raise Program_Error;
      end if;
   end Transform_Pragma_Check;

   function Transform_Pragma_Check
     (Prag  : Node_Id;
      Force : Boolean) return W_Prog_Id
   is
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
      --  pre / post / predicate are not handled here, unless Force is True

      if not Force and then Is_Ignored_Pragma_Check (Prag)
      then
         return New_Void (Prag);
      end if;

      Transform_Pragma_Check (Prag, Force, Check_Expr, Pred);

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

      --  Now handle remaining cases of "regular" pragma Check/Assert
      --  and pragma Assume. This is also how pragmas Preconditions and
      --  Postconditions inside a subprogram body are translated, as
      --  regular assertions.

      if Is_Pragma_Check (Prag, Name_Assume) then
         T := New_Assume_Statement (Pred => Pred);
      else
         T := New_Located_Assert (Prag, Pred, Reason, EW_Assert);
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

      function Get_Quantified_Variable
        (N          : Node_Id;
         Over_Range : Boolean) return Entity_Id;
      --  @return the entity representing the quantified variable of the
      --     quantification.

      function Get_Expr_Quantified_Over
        (N          : Node_Id;
         Over_Range : Boolean) return Node_Id;
      --  @return the expression over which quantification is performed

      function Make_Binding_For_Array
        (Ada_Node    : Node_Id;
         W_Arr_Expr  : W_Expr_Id;
         W_Index_Var : W_Identifier_Id;
         W_Quant_Var : W_Identifier_Id;
         Domain      : EW_Domain) return W_Expr_Id;
      --  @param Ada_Node quantified expression over an array
      --  @param W_Arr_Expr Why3 expression for the array value
      --  @param W_Index_Var Why3 name for the index of the quantification
      --  @param W_Quant_Var Why3 name for the quantified variable of the
      --     quantified expression in SPARK.
      --  @return the expression that binds the value of variable [W_Quant_Var]
      --     to the value of index variable [W_Index_Var]. For example, given
      --     a quantified expression (for all E of Arr => ...) and index
      --     variable J, it returns arr(j) suitably converted to E's type.

      function Make_Binding_For_Iterable
        (Ada_Node    : Node_Id;
         Container   : Node_Id;
         W_Index_Var : W_Identifier_Id;
         Domain      : EW_Domain;
         Element_T   : W_Type_Id;
         Params      : Transformation_Params) return W_Expr_Id;
      --  Constructs an expression that should be used to bind the index of a
      --  "of" quantified expression on a type with the Iterable aspect.
      --  Returns Element (Container, W_Index_Var)

      function Make_Constraint_For_Iterable
        (Ada_Node    : Node_Id;
         Container   : Node_Id;
         W_Index_Var : W_Expr_Id;
         Domain      : EW_Domain;
         Params      : Transformation_Params) return W_Expr_Id;
      --  Constructs an expression for the constraint of a quantified
      --  expression on a type with the Iterable aspect.
      --  Returns Has_Element (Container, W_Index_Var)

      -----------------------------
      -- Get_Quantified_Variable --
      -----------------------------

      function Get_Quantified_Variable
        (N          : Node_Id;
         Over_Range : Boolean) return Entity_Id
      is
      begin
         if Over_Range then
            return Defining_Identifier (Loop_Parameter_Specification (N));
         else
            return Defining_Identifier (Iterator_Specification (N));
         end if;
      end Get_Quantified_Variable;

      ------------------------------
      -- Get_Expr_Quantified_Over --
      ------------------------------

      function Get_Expr_Quantified_Over
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
      end Get_Expr_Quantified_Over;

      ----------------------------
      -- Make_Binding_For_Array --
      ----------------------------

      function Make_Binding_For_Array
        (Ada_Node    : Node_Id;
         W_Arr_Expr  : W_Expr_Id;
         W_Index_Var : W_Identifier_Id;
         W_Quant_Var : W_Identifier_Id;
         Domain      : EW_Domain) return W_Expr_Id
      is
         W_Acc_Expr : constant W_Expr_Id :=
           New_Array_Access (Ada_Node => Ada_Node,
                             Domain   => Domain,
                             Ar       => W_Arr_Expr,
                             Index    => (1 => +W_Index_Var));
      begin
         return Insert_Simple_Conversion (Domain => Domain,
                                          Expr   => W_Acc_Expr,
                                          To     => Get_Type (+W_Quant_Var));
      end Make_Binding_For_Array;

      -------------------------------
      -- Make_Binding_For_Iterable --
      -------------------------------

      function Make_Binding_For_Iterable
        (Ada_Node    : Node_Id;
         Container   : Node_Id;
         W_Index_Var : W_Identifier_Id;
         Domain      : EW_Domain;
         Element_T   : W_Type_Id;
         Params      : Transformation_Params) return W_Expr_Id
      is
         Element_E : constant Entity_Id :=
           Get_Iterable_Type_Primitive (Etype (Container), Name_Element);
         Cont_Type   : constant Entity_Id :=
           Etype (First_Entity (Element_E));
         Cont_Expr   : constant W_Expr_Id :=
           Insert_Simple_Conversion
             (Domain   => Domain,
              Expr     => Transform_Expr (Container, Domain, Params),
              To       => (if Use_Base_Type_For_Type (Cont_Type) then
                              Base_Why_Type (Cont_Type)
                           else Type_Of_Node (Cont_Type)));
         Curs_Type   : constant Entity_Id :=
           Etype (Next_Entity (First_Entity (Element_E)));
         Curs_Expr : constant W_Expr_Id :=
           Insert_Simple_Conversion
             (Ada_Node => Empty,
              Domain   => Domain,
              Expr     => +W_Index_Var,
              To       =>
                (if Use_Base_Type_For_Type (Curs_Type) then
                      Base_Why_Type (Curs_Type)
                 else Type_Of_Node (Curs_Type)));
      begin
         return New_VC_Call
           (Ada_Node => Ada_Node,
            Name     =>
                 W_Identifier_Id
                   (Transform_Identifier (Params       => Params,
                                          Expr         => Element_E,
                                          Ent          => Element_E,
                                          Domain       => Domain)),
            Progs    => (1 => Cont_Expr,
                         2 => Curs_Expr),
            Reason   => VC_Precondition,
            Domain   => Domain,
            Typ      => Element_T);
      end Make_Binding_For_Iterable;

      ----------------------------------
      -- Make_Constraint_For_Iterable --
      ----------------------------------

      function Make_Constraint_For_Iterable
        (Ada_Node    : Node_Id;
         Container   : Node_Id;
         W_Index_Var : W_Expr_Id;
         Domain      : EW_Domain;
         Params      : Transformation_Params) return W_Expr_Id
       is
         Subdomain   : constant EW_Domain :=
           (if Domain = EW_Pred then EW_Term else Domain);
         Has_Element : constant Entity_Id := Get_Iterable_Type_Primitive
           (Etype (Container), Name_Has_Element);
         T           : W_Expr_Id;
         Cont_Type   : constant Entity_Id :=
           Etype (First_Entity (Has_Element));
         Cont_Expr   : constant W_Expr_Id :=
           Insert_Simple_Conversion
             (Domain   => Subdomain,
              Expr     => Transform_Expr (Container, Subdomain, Params),
              To       => (if Use_Base_Type_For_Type (Cont_Type) then
                              Base_Why_Type (Cont_Type)
                           else Type_Of_Node (Cont_Type)));
         Curs_Type   : constant Entity_Id :=
           Etype (Next_Entity (First_Entity (Has_Element)));
         Curs_Expr  : constant W_Expr_Id :=
           Insert_Simple_Conversion
             (Ada_Node => Empty,
              Domain   => Subdomain,
              Expr     => +W_Index_Var,
              To       =>
                (if Use_Base_Type_For_Type (Curs_Type) then
                      Base_Why_Type (Curs_Type)
                 else Type_Of_Node (Curs_Type)));
      begin
         T := New_VC_Call
           (Ada_Node => Ada_Node,
            Name     =>
                 W_Identifier_Id
                   (Transform_Identifier (Params       => Params,
                                          Expr         => Has_Element,
                                          Ent          => Has_Element,
                                          Domain       => Subdomain)),
            Progs    => (1 => Cont_Expr,
                         2 => Curs_Expr),
            Reason   => VC_Precondition,
            Domain   => Subdomain,
            Typ      => Type_Of_Node (Etype (Has_Element)));

         if Domain = EW_Pred then
            T :=
              New_Call
                (Domain => Domain,
                 Typ    => EW_Bool_Type,
                 Name   => Why_Eq,
                 Args   => (T, +True_Term));
         end if;

         return T;
      end Make_Constraint_For_Iterable;

      --  We distinguish between 4 types of quantified expressions:
      --  . over a scalar range (for all V in Low .. High)
      --  . over an array (for all V of Arr)
      --  . over a container's content (for all V of Cont)
      --  . over a container's cursors (for all V in Cont)
      --  The boolean variables below correspond to these 4 mutually exclusive
      --  cases.

      Over_Range : constant Boolean :=
        Present (Loop_Parameter_Specification (Expr));

      Over_Array : constant Boolean :=
        Present (Iterator_Specification (Expr))
          and then Is_Iterator_Over_Array (Iterator_Specification (Expr));

      Over_Content : constant Boolean :=
        Present (Iterator_Specification (Expr))
          and then not Over_Array
          and then Of_Present (Iterator_Specification (Expr));

      Over_Cursors : constant Boolean :=
        Present (Iterator_Specification (Expr))
          and then not Over_Array
          and then not Over_Content;
      pragma Unreferenced (Over_Cursors);

      --  We distinguish the quantified variable from the index variable in our
      --  translation. For quantifications over a scalar range, they are the
      --  same. For quantifications over an array or a container of the form
      --  (for V of E) the quantified variable is V, and the index variable is
      --  the variable over which quantification is done in Why3, over the
      --  underlying scalar range for array/container E.

      Quant_Var  : Entity_Id;  --  Quantified variable for quantification
      Over_Expr  : Node_Id;    --  Expression over which quantification is done
      Quant_Type : Entity_Id;  --  Type of the quantified variable
      Bound_Expr : Node_Id;    --  Bound expression for the quantification
      Index_Type : Entity_Id;  --  Index type for the quantification

      W_Quant_Type : W_Type_Id;  --  Why3 type for the quantified variable
      W_Index_Type : W_Type_Id;  --  Why3 type for the index variable

      W_Over_Expr  : W_Expr_Id;  --  Why3 expression for the expression over
                                 --  which quantification is done. This is only
                                 --  used in those cases where the quantified
                                 --  and the index variables are not the same,
                                 --  thus needing binding between the two that
                                 --  relies on this expression.
      W_Bound_Expr : W_Expr_Id;  --  Why3 expression for the constraint giving
                                 --  the bounds over which quantification is
                                 --  done.
      Result       : W_Expr_Id;  --  Why3 expression for the quantification

      W_Quant_Var  : W_Identifier_Id;  --  Why3 name for the quantified
                                       --  variable.
      W_Index_Var  : W_Identifier_Id;  --  Why3 name for the index variable

   --  Start of processing for Transform_Quantified_Expression

   begin
      --  The usual translation of quantified expression into Why3 is as a
      --  predicate (Domain = EW_Pred), into a forall or exists quantification
      --  in Why3. For programs (Domain = EW_Prog), we also need to check the
      --  absence of run-time errors in sub-expressions. The case of terms
      --  (Domain in EW_Terms) appears when the quantified expression needs
      --  to be considered of type bool in Why3, for example because it is
      --  assigned into a Boolean variable in SPARK. In this case, we transform
      --  the quantified expression into a predicate, and convert this
      --  predicate (pred) into a term (if pred then True else False).

      if Domain in EW_Terms then
         declare
            Pred : constant W_Expr_Id :=
              Transform_Quantified_Expression (Expr, EW_Pred, Params);
         begin
            return Boolean_Expr_Of_Pred (+Pred, Domain);
         end;
      end if;

      --  Domain = EW_Pred or Domain = EW_Prog

      --  Step 1: extract relevant nodes and entities from the expression

      Quant_Var  := Get_Quantified_Variable (Expr, Over_Range);
      Over_Expr  := Get_Expr_Quantified_Over (Expr, Over_Range);
      Quant_Type := Etype (Quant_Var);

      if Over_Array then
         Bound_Expr := First_Index (Etype (Over_Expr));
      else
         Bound_Expr := Over_Expr;
      end if;

      if Over_Array then
         Index_Type := Etype (First_Index (Etype (Over_Expr)));
      elsif Over_Content then
         Index_Type := Get_Cursor_Type (Etype (Bound_Expr));
      else
         Index_Type := Etype (Quant_Var);
      end if;

      --  Step 2: create the base Why3 variables/expressions

      W_Quant_Type := (if Use_Base_Type_For_Type (Quant_Type) then
                          Base_Why_Type (Quant_Type)
                       else Type_Of_Node (Quant_Type));
      W_Index_Type := (if Use_Base_Type_For_Type (Index_Type) then
                          Base_Why_Type (Index_Type)
                       else Type_Of_Node (Index_Type));

      W_Quant_Var := New_Identifier (Name => Short_Name (Quant_Var),
                                     Typ  => W_Quant_Type);

      if Over_Array or Over_Content then
         W_Index_Var := New_Temp_Identifier (Typ => W_Index_Type);
      else
         W_Index_Var := W_Quant_Var;
      end if;

      if Over_Range or Over_Array then
         W_Bound_Expr := Range_Expr (Bound_Expr, +W_Index_Var, Domain, Params);
      else
         W_Bound_Expr :=
           +Make_Constraint_For_Iterable
             (Expr, Bound_Expr, +W_Index_Var, Domain, Params);
      end if;

      --  Step 3: translate the expression over which the quantification is
      --          applied, and save it in a temporary, which can then be
      --          referred to in any context (including predicates even when
      --          Domain = EW_Prog), which requires that the expression is
      --          first evaluated in the appropriate context to possibly
      --          generate run-time checks.

      if Over_Array or Over_Content then
         W_Over_Expr :=
           New_Temp_For_Expr
             (Transform_Expr
                (Over_Expr, Prog_Or_Term_Domain (Domain), Params));
      else
         W_Over_Expr := Why_Empty;  --  safe assignment in the unused case
      end if;

      --  Step 4: translate the condition in the quantified expression, in a
      --          context where the quantified variable is known.

      Ada_Ent_To_Why.Push_Scope (Symbol_Table);
      Insert_Entity (Quant_Var, W_Quant_Var);
      Result := Transform_Expr (Condition (Expr), Domain, Params);
      Ada_Ent_To_Why.Pop_Scope (Symbol_Table);

      --  Step 5: in those cases where the quantified variable and the index
      --          variable are not the same, wrap the result in an expression
      --          that gives a value to the quantified variable based on the
      --          value of the index variable.

      if Over_Array or Over_Content then
         declare
            W_Binding_Expr : W_Expr_Id;
         begin
            if Over_Array then
               W_Binding_Expr :=
                 Make_Binding_For_Array
                   (Expr, W_Over_Expr, W_Index_Var, W_Quant_Var,
                    Term_Domain (Domain));
            else --  Over_Content
               W_Binding_Expr :=
                 Make_Binding_For_Iterable
                   (Expr, Bound_Expr, +W_Index_Var,
                    Prog_Or_Term_Domain (Domain), W_Index_Type, Params);
            end if;

            Result := New_Typed_Binding (Domain  => Domain,
                                         Name    => W_Quant_Var,
                                         Def     => W_Binding_Expr,
                                         Context => Result);
         end;
      end if;

      --  Step 6: translate the quantified expression into a quantification in
      --          the predicate case, and an 'any' expression with a
      --          postcondition that uses the translation to predicate in the
      --          program case.

      if Domain = EW_Pred then
         declare
            Connector  : constant EW_Connector :=
              (if All_Present (Expr) then EW_Imply else EW_And);
            Quant_Body : constant W_Pred_Id :=
              New_Connection (Op    => Connector,
                              Left  => W_Bound_Expr,
                              Right => Result);
         begin
            if All_Present (Expr) then
               Result :=
                  New_Universal_Quantif
                     (Ada_Node  => Expr,
                      Variables => (1 => W_Index_Var),
                      Labels    => Name_Id_Sets.Empty_Set,
                      Var_Type  => W_Index_Type,
                      Pred      => Quant_Body);
            else
               Result :=
                  New_Existential_Quantif
                     (Ada_Node  => Expr,
                      Variables => (1 => W_Index_Var),
                      Labels    => Name_Id_Sets.Empty_Set,
                      Var_Type  => W_Index_Type,
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

      else  --  Domain = EW_Prog
         declare
            W_RTE : constant W_Prog_Id :=
              +New_Typed_Binding
                (Name    => W_Index_Var,
                 Domain  => EW_Prog,
                 Def     => +New_Simpl_Any_Prog (W_Index_Type),
                 Context =>
                   New_Conditional
                     (Domain    => EW_Prog,
                      Condition => W_Bound_Expr,
                      Then_Part => +New_Ignore (Prog => +Result)));
            W_Expr_Pred : constant W_Expr_Id :=
              Transform_Expr (Expr, EW_Pred, Params);
            W_Equiv : constant W_Expr_Id :=
              New_Connection
                (Domain   => EW_Pred,
                 Left     =>
                   New_Call (Domain => EW_Pred,
                             Name   => Why_Eq,
                             Typ    => EW_Bool_Type,
                             Args   => (+New_Result_Ident (EW_Bool_Type),
                                        +True_Term)),
                 Op       => EW_Equivalent,
                 Right    => W_Expr_Pred);
            W_Assume : constant W_Prog_Id :=
              New_Any_Statement (Ada_Node    => Expr,
                                 Return_Type => EW_Bool_Type,
                                 Post        => +W_Equiv);
         begin
            Result := +Sequence (W_RTE, W_Assume);
         end;
      end if;

      --  Step 7: possibly bind the value of the temporary introduced for
      --          the expression over which quantification is done.

      if Over_Array or Over_Content then
         Result := Binding_For_Temp (Ada_Node => Expr,
                                     Domain   => Domain,
                                     Tmp      => W_Over_Expr,
                                     Context  => Result);
      end if;

      return Result;
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
                   (Labels   => New_VC_Labels (Stat, VC_Raise),
                    Def      => +False_Pred),
                 Assert_Kind => EW_Assert);

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
            if not Inherited_Discriminant (Association) then
               CL := Choices (Association);
               Associated_Components := Associated_Components +
                 Integer (List_Length (CL));
            end if;
            Next (Association);
         end loop;
         return Associated_Components;
      end Components_Count;

      Component   : Entity_Id;
      Association : Node_Id;
      Field_Assoc :
        W_Field_Association_Array (1 .. Components_Count (Assocs));
      Num_Discr   : constant Integer :=
        (if Has_Discriminants (Typ) then
           Natural (Number_Discriminants (Typ))
         else 0);
      Discr_Assoc :
        W_Field_Association_Array (1 .. Num_Discr);
      Result      :
        W_Field_Association_Array (1 .. Components_Count (Assocs));
      Field_Index : Positive := 1;
      Discr_Index : Positive := 1;
      CL          : List_Id;
      Choice      : Node_Id;

   --  Start of processing for Transform_Record_Component_Associations

   begin
      --  Normal record aggregates are required to be fully initialized, but
      --  'Update aggregates are allowed to be partial. The implementation here
      --  is general enough for both kinds of aggregates so the association
      --  list does not necessarily cover all the components.

      pragma Assert
        (In_Attribute_Update
          or else Is_Tagged_Type (Typ)
          or else Number_Components (Typ) = List_Length (Assocs));

      Association := Nlists.First (Assocs);

      if No (Association) then
         return (1 .. 0 => <>);
      end if;

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

            --  Inherited discriminants in an extension aggregate are already
            --  accounted for in the ancestor part. Ignore them here.

            if not Inherited_Discriminant (Association) then
               Component := Search_Component_By_Name (Typ, Choice);
               pragma Assert (Present (Component));

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

               --  Attributes of component's type have default values of their
               --  type.

               if Has_Record_Type (Etype (Component))
                 or else Full_View_Not_In_SPARK (Etype (Component))
               then
                  Expr := New_Record_Attributes_Update
                    (Domain   => Domain,
                     Name     => Expr,
                     Ty       => Etype (Component));
               end if;

               if Ekind (Component) = E_Discriminant then
                  Discr_Assoc (Discr_Index) := New_Field_Association
                    (Domain => Domain,
                     Field  => To_Why_Id (Component),
                     Value  => Expr);
                  Discr_Index := Discr_Index + 1;
               else
                  Field_Assoc (Field_Index) := New_Field_Association
                    (Domain => Domain,
                     Field  => To_Why_Id (Component),
                     Value  => Expr);
                  Field_Index := Field_Index + 1;
               end if;
            end if;

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
      pragma Assert
        ((In_Attribute_Update and then Field_Index = Result'Last + 1)
         or else Is_Tagged_Type (Typ)
         or else Discr_Index = Discr_Assoc'Last + 1);
      Result := Discr_Assoc (1 .. Discr_Index - 1) &
        Field_Assoc (1 .. Field_Index - 1);
      return Result;
   end Transform_Record_Component_Associations;

   ------------------------------------
   -- Transform_Shift_Or_Rotate_Call --
   ------------------------------------

   function Transform_Shift_Or_Rotate_Call
     (Expr   : Node_Id;
      Domain : EW_Domain;
      Params : Transformation_Params) return W_Expr_Id
   is
      --  Define a convenient short hand for the test below
      function ECI (Left, Right : String) return Boolean
        renames Ada.Strings.Equal_Case_Insensitive;

      Subp        : constant Entity_Id := Entity (Sinfo.Name (Expr));
      Nb_Of_Refs  : Natural;
      Nb_Of_Lets  : Natural;

      Args        : constant W_Expr_Array :=
        Compute_Call_Args (Expr, Domain, Nb_Of_Refs, Nb_Of_Lets, Params);
      pragma Assert (Args'Length = 2);
      pragma Assert (Nb_Of_Refs = 0);
      pragma Assert (Nb_Of_Lets = 0);

      Modulus_Val : constant Uint := Modulus (Etype (Subp));
      Nb_Of_Bits  : constant Int := (if Modulus_Val = UI_Expon (2, 8) then
                                        8
                                     elsif Modulus_Val = UI_Expon (2, 16) then
                                        16
                                     elsif Modulus_Val = UI_Expon (2, 32) then
                                        32
                                     elsif Modulus_Val = UI_Expon (2, 64) then
                                        64
                                     else
                                        raise Program_Error);
      Typ         : constant W_Type_Id := (if Nb_Of_Bits = 8 then
                                              EW_BitVector_8_Type
                                           elsif Nb_Of_Bits = 16 then
                                              EW_BitVector_16_Type
                                           elsif Nb_Of_Bits = 32 then
                                              EW_BitVector_32_Type
                                           elsif Nb_Of_Bits = 64 then
                                              EW_BitVector_64_Type
                                           else raise Program_Error);
      T           : W_Expr_Id;

   begin
      --  ??? it is assumed that rotate calls are only valid on actual
      --  unsigned_8/16/32/64 types with the corresponding 'Size

      Get_Unqualified_Decoded_Name_String (Chars (Subp));

      declare
         Arg1   : constant W_Expr_Id := Args (Args'First);
         Arg2   : constant W_Expr_Id := Args (Args'First + 1);
         Arg2_M : constant W_Expr_Id :=
           Insert_Simple_Conversion (Domain => EW_Term,
                                     Expr   => Arg2,
                                     To     => Typ);
         Name_S : constant String    := Name_Buffer (1 .. Name_Len);
         Name   : constant W_Identifier_Id :=
           (if ECI (Name_S, Get_Name_String (Name_Shift_Right)) then
               MF_BVs (Typ).Lsr
            elsif ECI (Name_S,
              Get_Name_String (Name_Shift_Right_Arithmetic))
            then
               MF_BVs (Typ).Asr
            elsif ECI (Name_S, Get_Name_String (Name_Shift_Left)) then
               MF_BVs (Typ).Lsl
            elsif ECI (Name_S, Get_Name_String (Name_Rotate_Left)) then
               MF_BVs (Typ).Rotate_Left
            elsif ECI (Name_S, Get_Name_String (Name_Rotate_Right)) then
               MF_BVs (Typ).Rotate_Right
            else
               raise Program_Error);
         --         function Actual_Call (Amount : W_Expr_Id) return W_Expr_Id
      begin

         --  A special care need to be put in the case of shifts on a bitvector
         --  of size smaller than 32. Indeed, in this case the amount of
         --  the shift can be greater than 2**(Size of the underlying bv),
         --  resulting in a modulo on the amount of the shift Introduced by
         --  the convertion at the why3 level.
         if Nb_Of_Bits < 32
           and Name /= MF_BVs (Typ).Rotate_Left
           and Name /= MF_BVs (Typ).Rotate_Right
         then
            declare
               Nb_Of_Buits_UI : constant Uint := UI_From_Int (Nb_Of_Bits);
            begin
               T := New_Conditional
                 (Ada_Node    => Expr,
                  Domain      => EW_Term,
                  Condition   => New_Call
                    (Domain   => Domain,
                     Name     => Int_Infix_Lt,
                     Args     => (1 => Arg2,
                                  2 => New_Integer_Constant
                                    (Value => Nb_Of_Buits_UI)),
                     Typ      => EW_Bool_Type),
                  Then_Part   => New_Call
                       (Domain => EW_Term,
                        Name   => Name,
                        Args   =>
                          (1 => Arg1,
                           2 => Arg2_M),
                        Typ    => Typ),
                  Else_Part   =>
                    New_Modular_Constant (Value => Uint_0,
                                          Typ => Typ),
                  Typ         => Typ);
            end;
         else
            T := New_Call
              (Domain => EW_Term,
               Name   => Name,
               Args   => (1 => Arg1,
                          2 => Arg2_M),
               Typ    => Typ);
         end if;
      end;

      return T;
   end Transform_Shift_Or_Rotate_Call;

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
      Rng_Type  : constant W_Type_Id :=
        Base_Why_Type_No_Bool (Entity_Id'(Type_Of_Node (Low_Bound (Rng))));
      Low_Expr  : constant W_Expr_Id :=
        New_Temp_For_Expr
          (Transform_Expr (Low_Bound (Rng),
           Rng_Type,
           Domain,
           Params));
      High_Expr  : constant W_Expr_Id :=
        New_Temp_For_Expr
          (Transform_Expr (High_Bound (Rng),
           Rng_Type,
           Domain,
           Params));
   begin

      --  We start by translating the prefix itself.

      Pref_Expr := Transform_Expr (Prefx, Domain, Params);
      Pref_Expr := New_Temp_For_Expr (Pref_Expr);
      T := Pref_Expr;

      --  if needed, we convert the arrray to a simple base type

      if not Is_Static_Array_Type (Etype (Expr))
        and then
          not Is_Static_Array_Type (Get_Ada_Node (+Get_Type (Pref_Expr)))
        and then Get_Type_Kind (Get_Type (Pref_Expr)) /= EW_Split
      then
         T := Array_Convert_To_Base (Domain, T);
      end if;

      --  if needed, we insert a check that the slice bounds are in the bounds
      --  of the prefix

      if Domain = EW_Prog then
         declare
            Ar_Low   : constant W_Expr_Id :=
              Insert_Simple_Conversion
                (Domain => EW_Pred,
                 To     => Rng_Type,
                 Expr   => Get_Array_Attr (Domain => EW_Pred,
                                           Expr   => Pref_Expr,
                                           Attr   => Attribute_First,
                                           Dim    => 1));
            Ar_High  : constant W_Expr_Id :=
              Insert_Simple_Conversion
                (Domain => EW_Pred,
                 To     => Rng_Type,
                 Expr   => Get_Array_Attr (Domain => EW_Pred,
                                           Expr   => Pref_Expr,
                                           Attr   => Attribute_Last,
                                           Dim    => 1));
            Check    : constant W_Pred_Id :=
              New_Connection
                (Op     => EW_Imply,
                 Left   =>
                   New_Call
                     (Domain => EW_Pred,
                      Name   => (if Rng_Type = EW_Int_Type then
                                        Int_Infix_Le
                                 else
                                    MF_BVs (Rng_Type).Ule),
                      Typ    => EW_Bool_Type,
                      Args   => (+Low_Expr, +High_Expr)),
                 Right  =>
                   New_And_Then_Expr
                     (Domain => EW_Pred,
                      Left   =>
                        New_Range_Expr
                          (Domain => EW_Pred,
                           Low    => +Ar_Low,
                           High   => +Ar_High,
                           Expr   => Low_Expr),
                      Right =>
                        New_Range_Expr
                          (Domain => EW_Pred,
                           Low    => +Ar_Low,
                           High   => +Ar_High,
                           Expr   => +High_Expr)));
         begin
            T :=
              +Sequence (New_Located_Assert (Expr,
                         Check,
                         VC_Range_Check,
                         EW_Assert),
                         +T);
         end;
      end if;

      if Is_Static_Array_Type (Etype (Expr)) then

         --  a conversion may be needed to the target type

         T :=
           Insert_Array_Conversion
             (Domain         => Domain,
              Expr           => T,
              To             => Target_Ty,
              Force_No_Slide => True);

      --  when the slice bounds are not static, we produce a compound object
      --  contents + bounds.

      else
         T :=
           Array_Convert_From_Base
             (Domain => Domain,
              Ar     => T,
              Target => Get_Ada_Node (+Target_Ty),
              First  => Low_Expr,
              Last   => High_Expr);
      end if;
      T :=
        Binding_For_Temp
          (Domain  => Domain,
           Tmp     => Pref_Expr,
           Context => T);
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

      return T;
   end Transform_Slice;

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
                    Name     => M_Main.Return_Exc,
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
                            Params => Body_Params),
                          Typ      => Return_Type);
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
                    Name     => M_Main.Return_Exc);
               Expr        : W_Prog_Id :=
                 Transform_Statements_And_Declarations
                   (Return_Object_Declarations (Stmt_Or_Decl));
               Ret_Obj     : constant Entity_Id :=
                 Get_Return_Object (Stmt_Or_Decl);
               Ret_Type    : constant W_Type_Id :=
                 Type_Of_Node (Etype (Current_Subp));
               Obj_Deref   : constant W_Prog_Id :=
                 +Insert_Simple_Conversion
                   (Domain => EW_Prog,
                    Expr   => Transform_Identifier
                      (Params => Body_Params,
                       Expr   => Ret_Obj,
                       Ent    => Ret_Obj,
                       Domain => EW_Prog),
                    To     => Ret_Type);
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
                       Value => Obj_Deref,
                       Typ   => Ret_Type));
               return Sequence (Expr, Raise_Stmt);
            end;

         when N_Procedure_Call_Statement | N_Entry_Call_Statement =>
            declare
               Nb_Of_Refs : Natural;
               Nb_Of_Lets : Natural;
               Call       : W_Expr_Id;
               Subp       : constant Entity_Id :=
                 Get_Called_Entity (Stmt_Or_Decl);

               Args       : constant W_Expr_Array :=
                 Compute_Call_Args
                   (Stmt_Or_Decl, EW_Prog, Nb_Of_Refs, Nb_Of_Lets,
                    Params => Body_Params);

               Selector   : constant Selection_Kind :=
                  --  When calling an error-signaling procedure outside another
                  --  error-signaling procedure, use the No_Return variant of
                  --  the program function, which has a precondition of False.
                  --  This ensures that a check is issued for each such call,
                  --  to detect when they are reachable.

                 (if Is_Error_Signaling_Procedure (Subp)
                    and then not Is_Error_Signaling_Procedure (Current_Subp)
                  then
                     No_Return

                  --  When the call is dispatching, use the Dispatch variant of
                  --  the program function, which has the appropriate contract.

                  elsif Nkind (Stmt_Or_Decl) = N_Procedure_Call_Statement
                    and then Present (Controlling_Argument (Stmt_Or_Decl))
                  then
                     Dispatch

                  --  When the call has visibility over the refined
                  --  postcondition of the subprogram, use the Refine variant
                  --  of the program function, which has the appropriate
                  --  refined contract.

                  elsif Has_Contracts (Subp, Name_Refined_Post)
                    and then Has_Visibility_On_Refined (Stmt_Or_Decl, Subp)
                  then
                     Refine

                  --  Otherwise use the Standard variant of the program
                  --  function (defined outside any namespace, directly in
                  --  the module for the program function).

                  else Why.Inter.Standard);

               Why_Name   : constant W_Identifier_Id :=
                 W_Identifier_Id
                   (Transform_Identifier (Params   => Body_Params,
                                          Expr     => Stmt_Or_Decl,
                                          Ent      => Subp,
                                          Domain   => EW_Prog,
                                          Selector => Selector));
            begin
               if Why_Subp_Has_Precondition (Subp, Selector) then
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

               Call :=
                 +Sequence (Compute_Tag_Check (Stmt_Or_Decl, Body_Params),
                            +Call);

               if Nb_Of_Refs = 0 and then Nb_Of_Lets = 0 then
                  return +Call;
               else
                  return Insert_Ref_Context
                    (Body_Params, Stmt_Or_Decl, +Call,
                     Nb_Of_Refs, Nb_Of_Lets);
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
                               Name_Id_Sets.To_Set (New_Located_Label (Cur)),
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
                  Transform_Pragma_Check (Stmt_Or_Decl,
                                          Force   => False,
                                          Runtime => Check_Expr,
                                          Pred    => Pred);
                  Assert_And_Cut := Pred;
               end;
            end if;

            return Transform_Pragma (Stmt_Or_Decl, Force => False);

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

         --  Nothing to do for a number declaration

         when N_Number_Declaration =>
            return New_Void;

         --  Subprogram and package declarations are already taken care of
         --  explicitly. They should not be treated as part of a list of
         --  declarations.

         when N_Function_Instantiation
            | N_Package_Body
            | N_Package_Declaration
            | N_Procedure_Instantiation
            | N_Subprogram_Body
            | N_Subprogram_Declaration
            | N_Use_Package_Clause
            | N_Use_Type_Clause
            | N_Validate_Unchecked_Conversion =>
            return New_Void;

         --  delay statements can be ignored for proof

         when N_Delay_Until_Statement =>
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
                        (New_Located_Label (Stmt_Or_Decl)),
                      Def    => +Prog));
      if Cut_Assertion /= Why_Empty then
         Result :=
           New_Located_Abstract
             (Ada_Node => Stmt_Or_Decl,
              Expr     => +Result,
              Post     => Cut_Assertion,
              Reason   => VC_Assert);

         --  Assume the dynamic property of variables referenced in
         --  Cut_Assertion.
         --  ??? We should add the dynamic property of variables modified
         --  in the previous statements, but it is more difficult to get.

         declare
            Vars : constant Node_Sets.Set :=
              Compute_Ada_Node_Set (+Cut_Assertion);
         begin
            for V of Vars loop
               if Nkind (V) in N_Entity
                 and then Is_Object (V)
                 and then Entity_In_SPARK (V)
                 and then Ada_Ent_To_Why.Has_Element (Symbol_Table, V)
                 and then Is_Mutable_In_Why (V)
               then
                  Result := Sequence
                    (Result,
                     Assume_Dynamic_Invariant
                       (Expr          => +Transform_Identifier
                            (Params   => Body_Params,
                             Expr     => V,
                             Ent      => V,
                             Domain   => EW_Term),
                        Ty            => Etype (V),
                        Initialized   => False,
                        Only_Var      => True,
                        Top_Predicate => True));
               end if;
            end loop;
         end;
      end if;

      return Result;
   end Transform_Statement_Or_Declaration_In_List;

   -------------------------------------------
   -- Transform_Statements_And_Declarations --
   -------------------------------------------

   function Transform_Statements_And_Declarations
     (Stmts_And_Decls : List_Id) return W_Prog_Id
   is
      Cur_Stmt_Or_Decl : Node_Id   := Nlists.First (Stmts_And_Decls);
      Result           : W_Prog_Id := New_Void;

   begin
      while Present (Cur_Stmt_Or_Decl) loop
         Result :=
           Transform_Statement_Or_Declaration_In_List
             (Stmt_Or_Decl => Cur_Stmt_Or_Decl,
              Prev_Prog    => Result);

         Nlists.Next (Cur_Stmt_Or_Decl);
      end loop;

      return Result;
   end Transform_Statements_And_Declarations;

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
      Decl_File : Why_Section renames Why_Sections (Dispatch_Entity (N));
   begin
      if Params.File = Decl_File.File then
         Decl_File.Cur_Theory := Why_Empty;
      end if;

      Insert_Extra_Module
        (N,
         New_Module (File => No_Name, Name => NID (Name)));

      Open_Theory (Decl_File, E_Module (N),
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
   end Transform_String_Literal;

   -------------------------------
   -- Variables_In_Default_Init --
   -------------------------------

   procedure Variables_In_Default_Init
     (Ty        : Entity_Id;
      Variables : in out Flow_Id_Sets.Set) is
      Ty_Ext : constant Entity_Id := Retysp (Ty);
      Scope  : constant Flow_Scope := Get_Flow_Scope (Ty_Ext);
   begin
      if Is_Scalar_Type (Ty_Ext) then
         if Has_Default_Aspect (Ty_Ext) then
            Variables.Union
              (Get_Variable_Set
                 (N                    => Default_Aspect_Value (Ty_Ext),
                  Scope                => Scope,
                  Local_Constants      => Node_Sets.Empty_Set,
                  Fold_Functions       => False,
                  Use_Computed_Globals => True,
                  Reduced              => True));
         end if;
      elsif Is_Array_Type (Ty_Ext)
        and then Ekind (Ty_Ext) /= E_String_Literal_Subtype
      then
         pragma Assert (Is_Constrained (Ty_Ext));

         --  Generates:
         --  forall i1 : int ..
         --   in_range (i1) /\ .. ->
         --    get (<Expr>, i1, ...) = <Default_Component_Value>    <if any>
         --    default_init (get (<Expr>, i1, ...), Component_Type) <otherwise>

         if Has_Default_Aspect (Ty_Ext) then

            --  if Ty_Ext as a Default_Component_Value aspect,
            --  generate get (<Expr>, i1, ...) = <Default_Component_Value>

            Variables.Union
              (Get_Variable_Set
                 (N                    =>
                      Default_Aspect_Component_Value (Ty_Ext),
                  Scope                => Scope,
                  Local_Constants      => Node_Sets.Empty_Set,
                  Fold_Functions       => False,
                  Use_Computed_Globals => True,
                  Reduced              => True));
         else

            --  otherwise, use its Component_Type default value.

            Variables_In_Default_Init (Component_Type (Ty_Ext), Variables);
         end if;

      elsif Is_Record_Type (Ty_Ext) or else Is_Private_Type (Ty_Ext) then

         --  Generates:
         --  let tmp1 = <Expr>.rec__disc1 in
         --  <Expr>.is_constrained = False /\ <if Ty_Ext as default discrs>
         --  <Expr>.rec__disc1 = Discr1.default  <if Ty_Ext is unconstrained>
         --  <Expr>.rec__disc1 = Discr1 /\ ..    <if Ty_Ext is constrained>
         --  (check_for_field1 expr ->
         --      <Expr>.rec__field1 = Field1.def      <if Field1 has a default>
         --      default_init (<Expr>.rec__field1, Etype (Field1))) <otherwise>
         --  /\ ..

         declare
            Field  : Node_Id := (if Has_Discriminants (Ty_Ext)
                                 or else Has_Unknown_Discriminants (Ty_Ext)
                                 then First_Discriminant (Ty_Ext)
                                 else Empty);
            Elmt   : Elmt_Id :=
              (if Has_Discriminants (Ty_Ext)
               and then Is_Constrained (Ty_Ext)
               then First_Elmt (Stored_Constraint (Ty_Ext))
               else No_Elmt);
         begin

            --  Go through discriminants to create
            --  <Expr>.rec__disc1 = Discr1.default <if Ty_Ext is unconstrained>
            --  <Expr>.rec__disc1 = Discr1 /\ ..   <if Ty_Ext is constrained>

            while Present (Field) loop
               if not Is_Completely_Hidden (Field) then

                  if Is_Constrained (Ty_Ext) then

                     --  Generate <Expr>.rec__disc1 = Discr

                     Variables.Union
                       (Get_Variable_Set
                          (N                    => Node (Elmt),
                           Scope                => Scope,
                           Local_Constants      => Node_Sets.Empty_Set,
                           Fold_Functions       => False,
                           Use_Computed_Globals => True,
                           Reduced              => True));
                     Next_Elmt (Elmt);
                  else
                     pragma Assert (Has_Defaulted_Discriminants (Ty_Ext));

                     --  Generate <Expr>.rec__disc1 = Discr1.default

                     Variables.Union
                       (Get_Variable_Set
                          (N                    =>
                               Discriminant_Default_Value (Field),
                           Scope                => Scope,
                           Local_Constants      => Node_Sets.Empty_Set,
                           Fold_Functions       => False,
                           Use_Computed_Globals => True,
                           Reduced              => True));
                  end if;
               end if;
               Next_Discriminant (Field);
            end loop;

            --  Go through other fields to create the expression
            --  (check_for_field1 expr ->
            --   <Expr>.rec__field1 = Field1.def      <if Field1 has a default>
            --   default_init (<Expr>.rec__field1, Etype (Field1))) <otherwise>
            --  /\ ..

            if Is_Record_Type (Ty_Ext) or else Is_Private_Type (Ty_Ext) then
               Field := First_Component (Ty_Ext);

               while Present (Field) loop
                  if Component_Is_Visible_In_SPARK (Field) then
                     if Present (Expression (Parent (Field))) then

                        --  if Field has a default expression, use it.
                        --   <Expr>.rec__field1 = Field1.default

                        Variables.Union
                          (Get_Variable_Set
                             (N                    =>
                                  Expression (Parent (Field)),
                              Scope                => Scope,
                              Local_Constants      => Node_Sets.Empty_Set,
                              Fold_Functions       => False,
                              Use_Computed_Globals => True,
                              Reduced              => True));
                     else

                        --  otherwise, use its Field's Etype default value.
                        --   default_init (<Expr>.rec__field1, Etype (Field1)))

                        Variables_In_Default_Init (Etype (Field), Variables);
                     end if;
                  end if;

                  Next_Component (Field);
               end loop;
            end if;
         end;
      end if;

      --  Assume the default initial condition for Ty.

      if Has_Default_Init_Cond (Ty)
        or else Has_Inherited_Default_Init_Cond (Ty)
      then
         declare
            Default_Init_Subp : constant Entity_Id :=
              Default_Init_Cond_Procedure (Ty);
            Default_Init_Expr : constant Node_Id :=
              Get_Expr_From_Check_Only_Proc (Default_Init_Subp);
         begin
            if Present (Default_Init_Expr) then

               Variables.Union
                 (Get_Variable_Set
                    (N                    => Default_Init_Expr,
                     Scope                => Scope,
                     Local_Constants      => Node_Sets.Empty_Set,
                     Fold_Functions       => False,
                     Use_Computed_Globals => True,
                     Reduced              => True));
            end if;
         end;
      end if;
   end Variables_In_Default_Init;

   ------------------------------------
   -- Variables_In_Dynamic_Predicate --
   ------------------------------------

   procedure Variables_In_Dynamic_Predicate
     (Ty        : Entity_Id;
      Variables : in out Flow_Id_Sets.Set)
   is
      Ty_Ext : constant Entity_Id := Retysp (Ty);
      Scope  : constant Flow_Scope := Get_Flow_Scope (Ty_Ext);

      Dynamic_Pred_Subp : constant Entity_Id := Predicate_Function (Ty_Ext);
      Dynamic_Pred_Expr : constant Node_Id :=
        Get_Expr_From_Return_Only_Func (Dynamic_Pred_Subp);

   begin
      Variables.Union
        (Get_Variable_Set
           (N                    => Dynamic_Pred_Expr,
            Scope                => Scope,
            Local_Constants      => Node_Sets.Empty_Set,
            Fold_Functions       => False,
            Use_Computed_Globals => True,
            Reduced              => True));
   end Variables_In_Dynamic_Predicate;

   ------------------------------------
   -- Variables_In_Dynamic_Invariant --
   ------------------------------------

   procedure Variables_In_Dynamic_Invariant
     (Ty        : Entity_Id;
      Variables : in out Flow_Id_Sets.Set)
   is
      Ty_Ext : constant Entity_Id := Retysp (Ty);
      Scope  : constant Flow_Scope := Get_Flow_Scope (Ty_Ext);
   begin

      --  Dynamic property of the type itself

      if Type_Is_Modeled_As_Base (Ty_Ext) then

         --  If a scalar type is not modeled as base, then its bounds are
         --  constants.
         --  Otherwise, variables may occur in their expressions.

         declare
            Rng : constant Node_Id := Get_Range (Ty_Ext);
         begin
            Variables.Union
              (Get_Variable_Set
                 (N                    => Low_Bound (Rng),
                  Scope                => Scope,
                  Local_Constants      => Node_Sets.Empty_Set,
                  Fold_Functions       => False,
                  Use_Computed_Globals => True,
                  Reduced              => True));
            Variables.Union
              (Get_Variable_Set
                 (N                    => High_Bound (Rng),
                  Scope                => Scope,
                  Local_Constants      => Node_Sets.Empty_Set,
                  Fold_Functions       => False,
                  Use_Computed_Globals => True,
                  Reduced              => True));
         end;
      elsif Is_Array_Type (Ty_Ext)
        and then not Is_Static_Array_Type (Ty_Ext)
      then

         --  Variables coming from the bounds of the index types

         declare
            Index : Node_Id := First_Index (Ty_Ext);
         begin
            while Present (Index) loop
               if Type_Is_Modeled_As_Base (Etype (Index)) then
                  declare
                     Rng : constant Node_Id := Get_Range (Etype (Index));
                  begin
                     Variables.Union
                       (Get_Variable_Set
                          (N                    => Low_Bound (Rng),
                           Scope                => Scope,
                           Local_Constants      => Node_Sets.Empty_Set,
                           Fold_Functions       => False,
                           Use_Computed_Globals => True,
                           Reduced              => True));
                     Variables.Union
                       (Get_Variable_Set
                          (N                    => High_Bound (Rng),
                           Scope                => Scope,
                           Local_Constants      => Node_Sets.Empty_Set,
                           Fold_Functions       => False,
                           Use_Computed_Globals => True,
                           Reduced              => True));
                  end;
               end if;
               Next_Index (Index);
            end loop;
         end;

         --  If the array is constrained, also assume the value of its bounds

         if Is_Constrained (Ty_Ext) then
            declare
               Index : Node_Id := First_Index (Ty_Ext);
            begin
               while Present (Index) loop
                  declare
                     Rng       : constant Node_Id := Get_Range (Index);
                  begin
                     Variables.Union
                       (Get_Variable_Set
                          (N                    => Low_Bound (Rng),
                           Scope                => Scope,
                           Local_Constants      => Node_Sets.Empty_Set,
                           Fold_Functions       => False,
                           Use_Computed_Globals => True,
                           Reduced              => True));
                     Variables.Union
                       (Get_Variable_Set
                          (N                    => High_Bound (Rng),
                           Scope                => Scope,
                           Local_Constants      => Node_Sets.Empty_Set,
                           Fold_Functions       => False,
                           Use_Computed_Globals => True,
                           Reduced              => True));
                  end;
                  Next_Index (Index);
               end loop;
            end;
         end if;

      elsif Has_Discriminants (Ty_Ext)
        and then Is_Constrained (Ty_Ext)
      then

         --  Variables coming from the record's discriminants

         declare
            Discr     : Entity_Id := First_Discriminant (Ty_Ext);
            Elmt      : Elmt_Id := First_Elmt (Stored_Constraint (Ty_Ext));
         begin
            while Present (Discr) loop
               if Is_Not_Hidden_Discriminant (Discr) then
                  Variables.Union
                    (Get_Variable_Set
                       (N                    => Node (Elmt),
                        Scope                => Scope,
                        Local_Constants      => Node_Sets.Empty_Set,
                        Fold_Functions       => False,
                        Use_Computed_Globals => True,
                        Reduced              => True));
                  Next_Elmt (Elmt);
               end if;
               Next_Discriminant (Discr);
            end loop;
         end;
      end if;

      --  Variables in the predicate of the type

      if Has_Predicates (Ty_Ext) then
         Variables_In_Dynamic_Predicate (Ty_Ext, Variables);
      end if;

      --  Dynamic Invariant of Ty_Ext's components

      if Is_Array_Type (Ty_Ext)
        and then Ekind (Ty_Ext) /= E_String_Literal_Subtype
      then

         --  Generates:
         --  forall i1 .. in : int. in_range i1 /\ .. /\ in_range in ->
         --    Dynamic_Invariant (get <Expr> i1 .. in)

         Variables_In_Dynamic_Invariant (Component_Type (Ty_Ext), Variables);

      elsif Is_Record_Type (Ty_Ext) or else Is_Private_Type (Ty_Ext) then

         --  Generates:
         --  (check_for_f1 <Expr> -> Dynamic_Invariant <Expr>.rec__f1)
         --  /\ .. /\ (check_for_fn <Expr> -> Dynamic_Invariant <Expr>.rec__fn)
         --  As discriminants may occur in bounds of types of other fields,
         --  store them in the Symbol_Table.

         declare
            Field : Node_Id := First_Component_Or_Discriminant (Ty_Ext);
         begin
            while Present (Field) loop
               if (Is_Record_Type (Ty_Ext)
                   and then Component_Is_Visible_In_SPARK (Field))
                   or else (Ekind (Field) = E_Discriminant
                            and then Is_Not_Hidden_Discriminant (Field))
               then
                  Variables_In_Dynamic_Invariant (Etype (Field), Variables);
               end if;

               Next_Component_Or_Discriminant (Field);
            end loop;
         end;
      end if;
   end Variables_In_Dynamic_Invariant;

   -------------------------------
   -- Why_Subp_Has_Precondition --
   -------------------------------

   function Why_Subp_Has_Precondition
     (E        : Entity_Id;
      Selector : Selection_Kind := Why.Inter.Standard) return Boolean
   is
      Has_Precondition : constant Boolean :=
        Has_Contracts (E, Name_Precondition);
      Has_Classwide_Or_Inherited_Precondition : constant Boolean :=
        Has_Contracts (E, Name_Precondition,
                       Classwide => True,
                       Inherited => True);
   begin
      return (Selector /= Dispatch and Has_Precondition)
        or else Has_Classwide_Or_Inherited_Precondition
        or else Entity_In_Ext_Axioms (E)

        --  E is an error-signaling procedure called outside another
        --  error-signaling procedure (this is what the No_Return variant
        --  means) for which an implicit precondition of False is used.

        or else (Selector = No_Return and Is_Error_Signaling_Procedure (E));
   end Why_Subp_Has_Precondition;
end Gnat2Why.Expr;
