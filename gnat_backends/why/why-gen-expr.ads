------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                          W H Y - G E N - E X P R                         --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                       Copyright (C) 2010-2011, AdaCore                   --
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

with Types;     use Types;
pragma Warnings (Off);
--  ??? "Why.Types" is directly visible as "Types", as it has "Why" as a
--  common ancestor with the current package. So it hides compilation unit
--  with the same name ("Types"). Maybe we should think of renaming it to
--  "Why.W_Types".
with Why.Types; use Why.Types;
pragma Warnings (On);
with VC_Kinds;  use VC_Kinds;
with Why.Ids;   use Why.Ids;
with Why.Sinfo; use Why.Sinfo;

package Why.Gen.Expr is

   function Is_False_Boolean (P : W_Expr_Id) return Boolean;
   --  Check if the given program is the program "false"

   function Is_True_Boolean (P : W_Expr_Id) return Boolean;
   --  Check if the given program is the program "true"

   function New_And_Expr
      (Left, Right : W_Expr_Id;
       Domain      : EW_Domain) return W_Expr_Id;

   function New_And_Then_Expr
      (Left, Right : W_Expr_Id;
       Domain      : EW_Domain) return W_Expr_Id;

   function New_Comparison
     (Cmp         : EW_Relation;
      Left, Right : W_Expr_Id;
      Arg_Types   : W_Base_Type_Id;
      Domain      : EW_Domain)
     return W_Expr_Id;

   function New_Or_Expr
      (Left, Right : W_Expr_Id;
       Domain      : EW_Domain) return W_Expr_Id;

   function New_Or_Else_Expr
     (Left, Right : W_Expr_Id;
      Domain      : EW_Domain) return W_Expr_Id;

   function New_Simpl_Conditional
      (Condition : W_Expr_Id;
       Then_Part : W_Expr_Id;
       Else_Part : W_Expr_Id;
       Domain    : EW_Domain) return W_Expr_Id;
   --  Conditional, simplify if condition is true/false.

   function New_Located_Expr
      (Ada_Node : Node_Id;
       Expr     : W_Expr_Id;
       Reason   : VC_Kind;
       Domain   : EW_Domain) return W_Expr_Id;

   function New_Located_Call
      (Ada_Node : Node_Id;
       Name     : W_Identifier_Id;
       Progs    : W_Expr_Array;
       Reason   : VC_Kind;
       Domain   : EW_Domain) return W_Expr_Id;
   --  Build a program call with a fresh label corresponding to the Ada_Node.

   function New_Located_Label (N : Node_Id; Reason : VC_Kind)
      return W_Identifier_Id;
   --  Generate a label for the given Ada node.
   --
   --  This means: associate a fresh Why Identifier to the source location of
   --  the Ada Node, and return the identifier.

   function New_Simpl_Any_Expr
     (Domain   : EW_Domain;
      Arg_Type : W_Primitive_Type_Id) return W_Expr_Id;
   --  Build a "any" expression whose type is a simple type. In Prog domain,
   --  this is translated into an "any", and in the Term domain as an
   --  "epsilon".

   function New_Range_Expr
     (Domain    : EW_Domain;
      Low, High : W_Expr_Id;
      Expr      : W_Expr_Id) return W_Expr_Id;
   --  Build an expression (Low <= Expr and then Expr <= High), all
   --  comparisons being in "int"

   function New_Simpl_Any_Expr
     (Domain   : EW_Domain;
      Arg_Type : W_Primitive_Type_Id;
      Id       : W_Identifier_OId;
      Pred     : W_Pred_Id) return W_Expr_Id;

   function Insert_Conversion
      (Domain   : EW_Domain;
       Ada_Node : Node_Id := Empty;
       Expr     : W_Expr_Id;
       To       : W_Base_Type_Id;
       From     : W_Base_Type_Id;
       By       : W_Base_Type_OId := Why_Empty) return W_Expr_Id;

   --  We expect Expr to be of the type that corresponds to the type
   --  "From". We insert a conversion so that its type corresponds to "To".
   --  if "By" is non empty, then it specifies that the operation in expr
   --  is done in the corresponding base type and that its overflow check
   --  should be inserted.

end Why.Gen.Expr;
