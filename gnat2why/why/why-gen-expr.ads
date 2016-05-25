------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                          W H Y - G E N - E X P R                         --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                       Copyright (C) 2010-2016, AdaCore                   --
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

with Gnat2Why.Util;       use Gnat2Why.Util;
with Namet;               use Namet;
with Snames;              use Snames;
with Types;               use Types;
with Uintp;               use Uintp;
with VC_Kinds;            use VC_Kinds;
with Why.Atree.Builders;  use Why.Atree.Builders;
with Why.Ids;             use Why.Ids;
with Why.Sinfo;           use Why.Sinfo;

pragma Warnings (Off);
--  ??? "Why.Types" is directly visible as "Types", as it has "Why" as a
--  common ancestor with the current package. So it hides compilation unit
--  with the same name ("Types"). Maybe we should think of renaming it to
--  "Why.W_Types".
with Why.Types;           use Why.Types;
pragma Warnings (On);

package Why.Gen.Expr is

   function Is_False_Boolean (P : W_Expr_Id) return Boolean;
   --  Check if the given program is the program "false"

   function Is_True_Boolean (P : W_Expr_Id) return Boolean;
   --  Check if the given program is the program "true"

   function Bool_True (D : EW_Domain) return W_Expr_Id is
     (New_Literal (Value => EW_True, Domain => D));
   function Bool_False (D : EW_Domain) return W_Expr_Id is
     (New_Literal (Value => EW_False, Domain => D));

   function New_And_Expr
      (Left, Right : W_Expr_Id;
       Domain      : EW_Domain) return W_Expr_Id;

   function New_And_Expr
      (Left, Right : W_Expr_Id;
       Domain      : EW_Domain;
       Base        : W_Type_Id) return W_Expr_Id;
   --  Generate the expression "Left and Right"; choose the right "and"
   --  operation depending on "Base", e.g. for modular or boolean types.

   function New_And_Expr
     (Conjuncts : W_Expr_Array;
      Domain    : EW_Domain) return W_Expr_Id;

   function New_And_Then_Expr
      (Left, Right : W_Expr_Id;
       Domain      : EW_Domain) return W_Expr_Id;

   function New_Comparison
     (Symbol      : W_Identifier_Id;
      Left, Right : W_Expr_Id;
      Domain      : EW_Domain) return W_Expr_Id;

   function New_Ada_Equality
     (Typ              : Entity_Id;
      Domain           : EW_Domain;
      Left, Right      : W_Expr_Id;
      Force_Predefined : Boolean := False)
      return W_Expr_Id;
   --  generate a boolean term which expresses the translation of "Left =
   --  Right" in Ada semantics, where the equality is the one of type Typ.
   --  If the type has a user-provided primitive equality, use that. If
   --  Force_Predefined is True, pretend that the type does not have a
   --  user-provided primitive equality.

   function New_Or_Expr
     (Left, Right : W_Expr_Id;
      Domain      : EW_Domain) return W_Expr_Id;

   function New_Or_Expr
     (Left, Right : W_Expr_Id;
      Domain      : EW_Domain;
      Base        : W_Type_Id) return W_Expr_Id;
   --  Generate the expression "Left or Right"; choose the right "or" operation
   --  depending on "Base", e.g. for modular or boolean types.

   function New_Or_Expr
     (Conjuncts : W_Expr_Array;
      Domain    : EW_Domain) return W_Expr_Id;

   function New_Or_Else_Expr
     (Left, Right : W_Expr_Id;
      Domain      : EW_Domain) return W_Expr_Id;

   function New_Xor_Expr
      (Left, Right : W_Expr_Id;
       Domain      : EW_Domain;
       Base        : W_Type_Id) return W_Expr_Id;
   --  Build an expression "Left xor Right", and choose the right xor operation
   --  depending on "Base", which is either EW_Bool_Type or EW_Int_Type.

   function Why_Default_Value (Domain : EW_Domain; E : Entity_Id)
                               return W_Expr_Id;
   --  Return the default value for a given type

   function New_Simpl_Conditional
      (Condition : W_Expr_Id;
       Then_Part : W_Expr_Id;
       Else_Part : W_Expr_Id;
       Domain    : EW_Domain) return W_Expr_Id;
   --  Conditional, simplify if condition is true/false.

   function New_Located_Label
     (N         : Node_Id;
      Left_Most : Boolean := False) return Name_Id;
   --  Return a label that contains the Ada Sloc of the node

   function New_Shape_Label (Node : Node_Id) return Name_Id;
   --  Return a label representing the shape of the Ada code surrounding the
   --  input node. "Shapes" are more resistant to code refactorings than SLOCs
   --  of VCs. This makes Why3 proofs easier to replay. See Why3 VSTTE'13 paper
   --  for details.

   function New_Comment_Label
     (Node : Node_Id; Loc : Name_Id; Reason : VC_Kind) return Name_Id;
   --  Return a label with the tag "comment" in order to display VC information
   --  in VC generated files.

   function New_Sub_VC_Marker (N : Node_Id) return Name_Id;
   --  Return a label that contains the pretty printing for the given node

   function New_VC_Call
      (Ada_Node : Node_Id;
       Name     : W_Identifier_Id;
       Progs    : W_Expr_Array;
       Reason   : VC_Kind;
       Domain   : EW_Domain;
       Typ      : W_Type_Id) return W_Expr_Id;
   --  If we are not in the term domain, build a call with VC and location
   --  labels.

   function New_VC_Expr
      (Ada_Node   : Node_Id;
       Expr       : W_Expr_Id;
       Reason     : VC_Kind;
       Domain     : EW_Domain) return W_Expr_Id;
   --  If we are not in the "term" domain, put VC and location labels on the
   --  expression.

   function New_VC_Labels
     (N      : Node_Id;
      Reason : VC_Kind) return Name_Id_Set;
   --  Generate VC and location labels for the given Ada node, with the given
   --  VC reason

   function Cur_Subp_Sloc return Name_Id;
   --  Return a label that identifies the current subprogram or package

   function New_Range_Expr
     (Domain    : EW_Domain;
      Low, High : W_Expr_Id;
      Expr      : W_Expr_Id) return W_Expr_Id;
   --  Build an expression (Low <= Expr and then Expr <= High), all
   --  comparisons being in Base_Type (int or real)

   function New_Discrete_Add
     (Domain : EW_Domain;
      Left   : W_Expr_Id;
      Right  : W_Expr_Id;
      Typ    : W_Type_Id := Why_Empty) return W_Expr_Id;
   --  @param Left Right the operand of the operation.
   --  @return an addition in either the representation type of Typ or
   --          the representation type of left if Typ is left empty; This
   --          type should either be ew_int_type or a bitvector; Will
   --          do the appropriate convertion for left and right.
   --  beware that there is no modulo operation inserted when dealing
   --  with modulars.

   function New_Discrete_Substract
     (Domain : EW_Domain;
      Left   : W_Expr_Id;
      Right  : W_Expr_Id;
      Typ    : W_Type_Id := Why_Empty) return W_Expr_Id;
   --  @param Typ the type of the operation
   --  @param Left Right the operand of the operation.
   --  @return a substraction in either the representation type of Typ or
   --          the representation type of left if Typ is left empty; This
   --          type should either be ew_int_type or a bitvector; Will
   --          do the appropriate convertion for left and right.
   --  beware that there is no modulo operation inserted when dealing
   --  with modulars.

   function New_Discrete_Constant
     (Ada_Node : Node_Id := Empty;
      Value    : Uint;
      Typ      : W_Type_Id)
      return W_Expr_Id;
   --  @param Value the value of the constant
   --  @param Typ the type of the constant
   --  @return a modular constant if Typ satisfies Why_Type_Is_BitVector
   --          or an integer constant in all other cases.

   function New_Dynamic_Property
     (Domain : EW_Domain;
      Ty     : Entity_Id;
      Expr   : W_Expr_Id;
      Params : Transformation_Params := Body_Params) return W_Expr_Id;
   --  Function to generate a call expressing that Expr is of the dynamic type
   --  Ty

   function To_Int (D : EW_Domain; E : W_Expr_Id) return W_Expr_Id;
   --  Convert argument to int if not already done

   function Do_Range_Check
     (Ada_Node   : Node_Id;
      Ty         : Entity_Id;
      W_Expr     : W_Expr_Id;
      Check_Kind : Range_Check_Kind) return W_Prog_Id;
   --  Returns the Why program that does range checking on W_Expr, for type Ty.

   function Insert_Conversion_To_Rep_No_Bool
     (Domain : EW_Domain;
      Expr : W_Expr_Id)
      return W_Expr_Id;
   --  Convert argument to representation type or ew_int_id if expr is of
   --  type Bool.

   function Do_Index_Check
     (Ada_Node   : Node_Id;
      Arr_Expr   : W_Expr_Id;
      W_Expr     : W_Expr_Id;
      Dim        : Positive) return W_Prog_Id;
   --  Returns the Why program that does index checking on an index W_Expr in
   --  an array Arr_Expr.

   function Insert_Array_Conversion
     (Domain         : EW_Domain;
      Ada_Node       : Node_Id := Empty;
      Expr           : W_Expr_Id;
      To             : W_Type_Id;
      Need_Check     : Boolean := False;
      Force_No_Slide : Boolean := False)
      return W_Expr_Id;
   --  Generate a conversion between two Ada array types. If Range check
   --  is set, add a length or range check to the expression. Which
   --  kind of check, and against which type, is determined by calling
   --  [Gnat2why.Nodes.Get_Range_Check_Info] on the Range_Check node.

   function Insert_Checked_Conversion
     (Ada_Node : Node_Id;
      Domain   : EW_Domain;
      Expr     : W_Expr_Id;
      To       : W_Type_Id) return W_Expr_Id;
   --  Returns the expression of type To that converts Expr possibly inserting
   --  checks during the conversion.

   function Insert_Simple_Conversion
     (Ada_Node : Node_Id := Empty;
      Domain   : EW_Domain;
      Expr     : W_Expr_Id;
      To       : W_Type_Id;
      Force_No_Slide : Boolean := False) return W_Expr_Id;
   --  Returns the expression of type To that converts Expr of type From. No
   --  check is inserted in the conversion.

   function Insert_Scalar_Conversion
     (Domain      : EW_Domain;
      Ada_Node    : Node_Id := Empty;
      Expr        : W_Expr_Id;
      To          : W_Type_Id;
      Do_Check    : Boolean := False) return W_Expr_Id;
   --  We insert a conversion on Expr so that its type corresponds to "To".
   --  When Range_Check is set, a range check is inserted into the conversion,
   --  and the node Ada_Node is used to determine the kind of the check.

   function Insert_Scalar_Conversion
     (Domain        : EW_Domain;
      Ada_Node      : Node_Id := Empty;
      Expr          : W_Expr_Id;
      To            : W_Type_Id;
      Range_Type    : Entity_Id;
      Check_Kind    : Range_Check_Kind) return W_Expr_Id;
   --  Same as the above except that we take directly the kind of check as
   --  input.

   function Insert_Record_Conversion
     (Ada_Node   : Node_Id;
      Domain     : EW_Domain;
      Expr       : W_Expr_Id;
      To         : W_Type_Id;
      Need_Check : Boolean := False) return W_Expr_Id;
   --  when Discr_Check is set, a discriminant check is inserted into the
   --  conversion, and the node is used to determine the subtype for the check.

   function New_Typed_Binding
     (Ada_Node : Node_Id := Empty;
      Domain   : EW_Domain;
      Name     : W_Identifier_Id;
      Def      : W_Expr_Id;
      Context  : W_Expr_Id)
      return W_Expr_Id;
   --  same as New_Binding, but adds type information coming from Context

   subtype Supported_Attribute_Id is Attribute_Id with
     Static_Predicate => Supported_Attribute_Id in Attribute_Alignment
                                                 | Attribute_Constrained
                                                 | Attribute_First
                                                 | Attribute_Last
                                                 | Attribute_Length
                                                 | Attribute_Modulus
                                                 | Attribute_Image
                                                 | Attribute_Value
                                                 | Attribute_Size
                                                 | Attribute_Component_Size
                                                 | Attribute_Tag;

   function New_Attribute_Expr
     (Ty        : Entity_Id;
      Domain    : EW_Domain;
      Attr      : Supported_Attribute_Id;
      Params    : Transformation_Params := Body_Params) return W_Expr_Id;
   --  Compute an expression for a type attribute Ty'Attr.
   --  @param Ty The entity for the Ada type.
   --  @param Domain The domain of the returned expression.
   --  @param Attr The querried type attribute.
   --  @param Params The parameters used for the transformation of bound
   --  expressions.
   --  @return The translated type attribute into Why3.

   function Get_Type (E : W_Expr_Id) return W_Type_Id;
   --  extract the type of a given expression

   function New_Havoc_Call (Id : W_Identifier_Id) return W_Prog_Id;
   --  @param Id Identifier of a variable
   --  @result Program havocing the value of Id

   -------------------------------------
   -- Introducing temporary variables --
   -------------------------------------

   --  The following two functions are intended to be used as follows:
   --  Tmp : W_Expr_Id := New_Temp_For_Expr (E);
   --  .... build a complex expression R using Tmp ...
   --  Result : W_Expr_Id := Binding_For_Temp (Tmp, R);

   --  the result is that a temporary variable is introduced (when necessary)
   --  for E, which is used in the complex expression. The user of these two
   --  functions just uses "Tmp" everywhere and can forget about "E". The call
   --  to Binding_For_Temp puts the let-binding on top of the resulting term,
   --  or simply returns "Context" when no temp was in fact necessary.

   function New_Temp_For_Expr
     (E         : W_Expr_Id;
      Need_Temp : Boolean := True) return W_Expr_Id;
   --  Return a temp variable for the given expression, and store the provided
   --  expression for later use. If Need_Temp is False, do not actually
   --  introduce a temp variable.

   function Binding_For_Temp
     (Ada_Node : Node_Id := Empty;
      Domain   : EW_Domain;
      Tmp      : W_Expr_Id;
      Context  : W_Expr_Id) return W_Expr_Id;
   --  Introduce a let binding for Tmp on top of "Context". The value of Tmp is
   --  the one provided to the corresponding call to New_Temp_For_Expr.

end Why.Gen.Expr;
