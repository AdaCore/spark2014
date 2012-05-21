------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                          W H Y - G E N - E X P R                         --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                       Copyright (C) 2010-2012, AdaCore                   --
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
with Snames;         use Snames;
with Types;          use Types;
pragma Warnings (Off);
--  ??? "Why.Types" is directly visible as "Types", as it has "Why" as a
--  common ancestor with the current package. So it hides compilation unit
--  with the same name ("Types"). Maybe we should think of renaming it to
--  "Why.W_Types".
with Why.Types;      use Why.Types;
pragma Warnings (On);
with VC_Kinds;       use VC_Kinds;

with Gnat2Why.Nodes; use Gnat2Why.Nodes;
with Why.Ids;        use Why.Ids;
with Why.Sinfo;      use Why.Sinfo;

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

   function New_Xor_Expr
      (Left, Right : W_Expr_Id;
       Domain      : EW_Domain) return W_Expr_Id;

   function New_Simpl_Conditional
      (Condition : W_Expr_Id;
       Then_Part : W_Expr_Id;
       Else_Part : W_Expr_Id;
       Domain    : EW_Domain) return W_Expr_Id;
   --  Conditional, simplify if condition is true/false.

   function New_Located_Label (N : Node_Id) return W_Identifier_Id;
   --  Return a label that contains the Ada Sloc of the node

   function New_Located_Expr (Ada_Node : Node_Id;
                              Expr     : W_Expr_Id;
                              Domain   : EW_Domain) return W_Expr_Id;
   --  put a location label on the given expression

   function New_VC_Call
      (Ada_Node : Node_Id;
       Name     : W_Identifier_Id;
       Progs    : W_Expr_Array;
       Reason   : VC_Kind;
       Domain   : EW_Domain) return W_Expr_Id;
   --  If we are not in the term domain, build a call with VC and location
   --  labels.

   function New_VC_Expr
      (Ada_Node : Node_Id;
       Expr     : W_Expr_Id;
       Reason   : VC_Kind;
       Domain   : EW_Domain) return W_Expr_Id;
   --  If we are not in the "term" domain, put VC and location labels on the
   --  expression.

   function New_VC_Labels (N : Node_Id; Reason : VC_Kind)
      return W_Identifier_Array;
   --  Generate VC and location labels for the given Ada node, with the given
   --  VC reason

   function New_Range_Expr
     (Domain    : EW_Domain;
      Base_Type : W_Base_Type_Id;
      Low, High : W_Expr_Id;
      Expr      : W_Expr_Id) return W_Expr_Id;
   --  Build an expression (Low <= Expr and then Expr <= High), all
   --  comparisons being in Base_Type (int or real)

   function Insert_Conversion
     (Domain        : EW_Domain;
      Ada_Node      : Node_Id := Empty;
      Expr          : W_Expr_Id;
      To            : W_Base_Type_Id;
      From          : W_Base_Type_Id;
      Overflow_Type : W_Base_Type_OId := Why_Empty;
      Range_Type    : W_Base_Type_OId := Why_Empty) return W_Expr_Id
   with
     Pre => Overflow_Type = Why_Empty or else Range_Type = Why_Empty;
   --  We expect Expr to be of the type that corresponds to the type "From".
   --  We insert a conversion so that its type corresponds to "To". If
   --  Overflow_Type is non empty, then it specifies that the operation in
   --  expr is done in the corresponding base type and that its overflow check
   --  should be inserted. If Range_Type is non empty, then a range check
   --  should be inserted that the result is in the bounds of this type. Both
   --  of Overflow_Type and Range_Type should not be set at the same time.

   function New_Attribute_Expr (Ty : Entity_Id; Attr : Attribute_Id)
                                return W_Expr_Id;

   function Compute_Ada_Nodeset (W : Why_Node_Id) return
     Node_Sets.Set;
   --  For a given Why node, compute the required Ada nodes, from which we can
   --  compute the necessary inclusions on the Why side

end Why.Gen.Expr;
