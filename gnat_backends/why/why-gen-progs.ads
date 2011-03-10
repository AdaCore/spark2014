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
-- gnat2why is  free  software;  you can redistribute it and/or modify it   --
-- under terms of the  GNU General Public License as published  by the Free --
-- Software Foundation;  either version  2,  or  (at your option) any later --
-- version. gnat2why is distributed in the hope that it will  be  useful,   --
-- but WITHOUT ANY WARRANTY; without even the implied warranty of MERCHAN-  --
-- TABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public --
-- License  for more details. You  should  have  received a copy of the GNU --
-- General Public License  distributed with GNAT; see file COPYING. If not, --
-- write to the Free Software Foundation,  51 Franklin Street, Fifth Floor, --
-- Boston,                                                                  --
--                                                                          --
-- gnat2why is maintained by AdaCore (http://www.adacore.com)               --
--                                                                          --
------------------------------------------------------------------------------

with Namet;         use Namet;
with Types;         use Types;
with Why.Gen.Types; use Why.Gen.Types;
with Why.Ids;       use Why.Ids;
with Why.Sinfo;     use Why.Sinfo;

package Why.Gen.Progs is

   function Conversion_Name
      (From : Why_Type;
       To   : Why_Type) return W_Identifier_Id
      with Pre =>
        (not (From = To) and then
         (From.Kind = Why_Int or else To.Kind = Why_Int));
   --  Return the name of the conversion function between the two types

   function Insert_Conversion
      (Ada_Node : Node_Id := Empty;
       To       : Why_Type;
       From     : Why_Type;
       Why_Expr : W_Prog_Id) return W_Prog_Id;
   --  We expect Why_Expr to be of the type that corresponds to the type
   --  "From". We insert a conversion so that its type corresponds to "To".

   function New_Assume_Statement
      (Ada_Node : Node_Id;
       Pred     : W_Predicate_Id)
       return W_Prog_Id;
   --  Generate an assumption statement. There is no such thing in Why2, so it
   --  is encoded as follows:
   --    [ unit -> { true } unit { P} ] void

   function New_For_Loop
     (Ada_Node   : Node_Id;
      Loop_Index : Name_Id;
      Low        : W_Prog_Id;
      High       : W_Prog_Id;
      Invariant  : W_Loop_Annot_Id;
      Loop_Body  : W_Prog_Id) return W_Prog_Id;
   --  Generate a for loop in Why. Use an encoding of the following form:
   --  let i = ref start in
   --  while in_range(!i) do
   --    ..
   --    i := !i + 1;
   --  done
   --  Low and High should be of type Why_Int

   function New_Located_Assert
      (Ada_Node : Node_Id;
       Pred     : W_Predicate_Id) return W_Prog_Id;
   --  Build a named assert (in programs) of a predicate

   function New_Located_Call
      (Ada_Node : Node_Id;
       Name     : W_Identifier_Id;
       Progs    : W_Prog_Array) return W_Prog_Id;
   --  Build a program call with a fresh label corresponding to the Ada_Node.

   function New_Prog_Andb (Left, Right : W_Prog_Id) return W_Prog_Id;
   --  Build a boolean disjunction as program.

   function New_Prog_Boolean_Cmp (Cmp : W_Relation; Left, Right : W_Prog_Id)
      return W_Prog_Id;
   --  Build a boolean comparison for programs of "int" type.

   function New_Prog_Orb (Left, Right : W_Prog_Id) return W_Prog_Id;
   --  Build a boolean disjunction as program.

   function New_Void (Ada_Node : Node_Id := Empty) return W_Prog_Id;
   --  The program "void"
   --
   function Sequence (Left, Right : W_Prog_Id) return W_Prog_Id;
   --  Build a statement sequence of the two arguments, but try to minimize
   --  nesting of W_Statement_Sequence constructors.
end Why.Gen.Progs;
