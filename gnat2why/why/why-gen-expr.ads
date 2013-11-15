------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                          W H Y - G E N - E X P R                         --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                       Copyright (C) 2010-2013, AdaCore                   --
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

with Namet;               use Namet;
with Snames;              use Snames;
with Types;               use Types;
with Why.Atree.Builders;  use Why.Atree.Builders;
pragma Warnings (Off);
--  ??? "Why.Types" is directly visible as "Types", as it has "Why" as a
--  common ancestor with the current package. So it hides compilation unit
--  with the same name ("Types"). Maybe we should think of renaming it to
--  "Why.W_Types".
with Why.Types;           use Why.Types;
pragma Warnings (On);
with VC_Kinds;            use VC_Kinds;

with Why.Ids;             use Why.Ids;
with Why.Sinfo;           use Why.Sinfo;

with Gnat2Why.Nodes;      use Gnat2Why.Nodes;

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
     (Cmp         : EW_Relation;
      Left, Right : W_Expr_Id;
      Domain      : EW_Domain)
      return W_Expr_Id;

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
      Is_VC     : Boolean;
      Left_Most : Boolean := False) return Name_Id;
   --  Return a label that contains the Ada Sloc of the node

   function New_Pretty_Label (N : Node_Id) return Name_Id;
   --  Return a label that contains the pretty printing for the given node

   function New_Located_Expr
     (Ada_Node : Node_Id;
      Expr     : W_Expr_Id;
      Domain   : EW_Domain;
      Is_VC    : Boolean) return W_Expr_Id;
   --  put a location label on the given expression

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
      (Ada_Node : Node_Id;
       Expr     : W_Expr_Id;
       Reason   : VC_Kind;
       Domain   : EW_Domain) return W_Expr_Id;
   --  If we are not in the "term" domain, put VC and location labels on the
   --  expression.

   function New_VC_Labels
     (N      : Node_Id;
      Reason : VC_Kind) return Name_Id_Set;
   --  Generate VC and location labels for the given Ada node, with the given
   --  VC reason

   function Cur_Subp_Sloc return Name_Id;
   --  Return a label that identifies the current subprogram or package

   function Cur_Subp_Name_Label return Name_Id;
   --  Return a label that contains the name of the current subprogram or
   --  package.

   function New_Range_Expr
     (Domain    : EW_Domain;
      Low, High : W_Expr_Id;
      Expr      : W_Expr_Id) return W_Expr_Id;
   --  Build an expression (Low <= Expr and then Expr <= High), all
   --  comparisons being in Base_Type (int or real)

   function New_Int_Add
     (Domain : EW_Domain;
      Left   : W_Expr_Id;
      Right  : W_Expr_Id) return W_Expr_Id;
   --  Function to build Left + Right with integer addition; will convert Left
   --  and Right to "int" if necessary

   function New_Int_Substract
     (Domain : EW_Domain;
      Left   : W_Expr_Id;
      Right  : W_Expr_Id) return W_Expr_Id;
   --  Function to build Left - Right with integer addition; will convert Left
   --  and Right to "int" if necessary

   function To_Int (D : EW_Domain; E : W_Expr_Id) return W_Expr_Id;
   --  Convert argument to int if not already done

   function Do_Range_Or_Index_Check
     (Ada_Node   : Node_Id;
      Ty         : Entity_Id;
      W_Expr     : W_Expr_Id;
      Check_Kind : Range_Check_Kind) return W_Prog_Id;
   --  Returns the Why program that does range of index checking on W_Expr, for
   --  type Ty.

   function Insert_Array_Conversion
     (Domain     : EW_Domain;
      Ada_Node   : Node_Id := Empty;
      Expr       : W_Expr_Id;
      To         : W_Type_Id;
      Need_Check : Boolean := False) return W_Expr_Id;
   --  Generate a conversion between two Ada array types. If Range check
   --  is set, add a length or range check to the expression. Which
   --  kind of check, and against which type, is determined by calling
   --  [Gnat2why.Nodes.Get_Range_Check_Info] on the Range_Check node.

   function Insert_Checked_Conversion
     (Ada_Node : Node_Id;
      Ada_Type : Entity_Id;
      Domain   : EW_Domain;
      Expr     : W_Expr_Id;
      To       : W_Type_Id) return W_Expr_Id;
   --  Returns the expression of type To that converts Expr of type From,
   --  possibly inserting checks during the conversion.

   function Insert_Simple_Conversion
     (Ada_Node : Node_Id := Empty;
      Domain   : EW_Domain;
      Expr     : W_Expr_Id;
      To       : W_Type_Id) return W_Expr_Id;
   --  Returns the expression of type To that converts Expr of type From. No
   --  check is inserted in the conversion.

   function Insert_Scalar_Conversion
     (Domain      : EW_Domain;
      Ada_Node    : Node_Id := Empty;
      Expr        : W_Expr_Id;
      To          : W_Type_Id;
      Round_Func  : W_Identifier_Id := Why_Empty;
      Range_Check : Node_Id := Empty) return W_Expr_Id;
   --  We expect Expr to be of the type that corresponds to the type "From".
   --  We insert a conversion so that its type corresponds to "To".
   --  When Round_Func is set, a call to the rounding function is inserted
   --  into the conversion, on the argument of type "real".
   --  When Range_Check is set, a range check is inserted into the conversion,
   --  and the node is used to determine the kind of the check.

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

   function New_Attribute_Expr
     (Ty   : Entity_Id;
      Attr : Attribute_Id) return W_Expr_Id;

   function Get_Type (E : W_Expr_Id) return W_Type_Id;
   --  extract the type of a given expression

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
   --  expression for later use. If Need_Temp is set, do not actually introduce
   --  a temp variable.

   function Binding_For_Temp
     (Ada_Node : Node_Id := Empty;
      Domain   : EW_Domain;
      Tmp      : W_Expr_Id;
      Context  : W_Expr_Id)
      return W_Expr_Id;
   --  Introduce a let binding for Tmp on top of "Context". The value of Tmp is
   --  the one provided to the corresponding call to New_Temp_For_Expr.

end Why.Gen.Expr;
