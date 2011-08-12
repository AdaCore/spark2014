------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                        W H Y - G E N - P R O G S                         --
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

with Types;              use Types;
with VC_Kinds;           use VC_Kinds;
with Why.Atree.Builders; use Why.Atree.Builders;
with Why.Ids;            use Why.Ids;
with Why.Inter;          use Why.Inter;
with Why.Sinfo;          use Why.Sinfo;

package Why.Gen.Progs is

   function Conversion_Name
      (From : Why_Type;
       To   : Why_Type) return W_Identifier_Id
      with Pre =>
        (not (From = To) and then
         (From.Kind in Why_Scalar_Enum or else To.Kind in Why_Scalar_Enum));
   --  Return the name of the conversion function between the two types

   function Insert_Conversion
      (Ada_Node : Node_Id := Empty;
       To                    : Why_Type;
       From                  : Why_Type;
       Why_Expr              : W_Prog_Id;
       Base_Type              : Why_Type := Why_Int_Type)
       return W_Prog_Id;
   --  We expect Why_Expr to be of the type that corresponds to the type
   --  "From". We insert a conversion so that its type corresponds to "To".
   --  If Base_Type is set to "int", nothing else happens. Otherwise, if
   --  From and to are set to "int", we insert a check that the result belongs
   --  to the range of the Base_Type.

   function New_Assume_Statement
      (Ada_Node    : Node_Id;
       Pred        : W_Predicate_Id;
       Return_Type : W_Primitive_Type_Id :=
                       New_Base_Type (Base_Type => EW_Unit))
       return W_Prog_Id;
   --  Generate an assumption statement. There is no such thing in Why2, so it
   --  is encoded as follows:
   --    [ { true } <return_type> { P} ]

   function New_For_Loop
     (Ada_Node   : Node_Id;
      Loop_Index : W_Identifier_Id;
      Low        : W_Identifier_Id;
      High       : W_Identifier_Id;
      Invariant  : W_Predicate_Id;
      Loop_Body  : W_Prog_Id) return W_Prog_Id;
   --  Generate a for loop in Why. Use an encoding of the following form:
   --  let i = ref start in
   --  while in_range(!i) do
   --    ..
   --    i := !i + 1;
   --  done
   --  Low and High are identifiers that represent the bounds of the range

   function New_Ignore (Ada_Node : Node_Id := Empty; Prog : W_Prog_Id)
      return W_Prog_Id;
   --   Build the program "ignore(prog)" of return type "unit".

   function New_Located_Assert
      (Ada_Node : Node_Id;
       Pred     : W_Predicate_Id) return W_Prog_Id;
   --  Build a named assert (in programs) of a predicate

   function New_Located_Call
      (Ada_Node : Node_Id;
       Name     : W_Identifier_Id;
       Progs    : W_Expr_Array;
       Reason   : VC_Kind) return W_Prog_Id;
   --  Build a program call with a fresh label corresponding to the Ada_Node.

   function New_Prog_Andb (Left, Right : W_Prog_Id) return W_Prog_Id;
   --  Build a boolean conjunction as program.

   function New_Prog_Andb_Then (Left, Right : W_Prog_Id) return W_Prog_Id;
   --  Build a boolean conjunction as program.

   function New_Prog_Boolean_Cmp
     (Cmp         : EW_Relation;
      Left, Right : W_Prog_Id)
     return W_Prog_Id;
   --  Build a boolean comparison for programs of "int" type.

   function New_Prog_Notb (Right : W_Prog_Id) return W_Prog_Id;
   --  Build a boolean negation as a program.

   function New_Prog_Orb (Left, Right : W_Prog_Id) return W_Prog_Id;
   --  Build a boolean disjunction as program.

   function New_Prog_Orb_Else (Left, Right : W_Prog_Id) return W_Prog_Id;
   --  Build a boolean disjunction as program.

   function New_Simpl_Any_Expr (T : W_Primitive_Type_Id) return W_Prog_Id;
   --  Build a "any" expression whose type is a simple type.

   function New_Simpl_Conditional_Prog
      (Condition : W_Prog_Id;
       Then_Part : W_Prog_Id;
       Else_Part : W_Prog_Id) return W_Prog_Id;
   --  Conditional program, simplify if condition is true/false.

   function New_True_Literal_Prog (Ada_Node : Node_Id := Empty)
      return W_Prog_Id;
   --  Return the program consisting of the boolean constant "true".

   function Sequence (Left, Right : W_Prog_Id) return W_Prog_Id;
   --  Build a statement sequence of the two arguments, but try to minimize
   --  nesting of W_Statement_Sequence constructors.

   function New_Result
     (T : W_Simple_Value_Type_Id)
     return W_Binder_Id;

end Why.Gen.Progs;
