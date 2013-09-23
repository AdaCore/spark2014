------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                        W H Y - G E N - P R O G S                         --
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

with Types;               use Types;
with VC_Kinds;            use VC_Kinds;

with Why.Atree.Builders;  use Why.Atree.Builders;
with Why.Ids;             use Why.Ids;
with Why.Sinfo;           use Why.Sinfo;
with Why.Types;           use Why.Types;
with Why.Gen.Preds;       use Why.Gen.Preds;

package Why.Gen.Progs is

   True_Prog  : constant W_Prog_Id := New_Literal (Value => EW_True);
   False_Prog : constant W_Prog_Id := New_Literal (Value => EW_False);

   function New_Assume_Statement
     (Ada_Node    : Node_Id := Empty;
      Pre         : W_Pred_Id := True_Pred;
      Post        : W_Pred_Id;
      Return_Type : W_Base_Type_Id := Why_Empty)
       return W_Prog_Id;
   --  Generate an assumption statement. There is no such thing in Why2, so it
   --  is encoded as follows:
   --    [ { true } <return_type> { P} ]

   function New_For_Loop
     (Ada_Node   : Node_Id;
      Loop_Index : W_Identifier_Id;
      Low        : W_Identifier_Id;
      High       : W_Identifier_Id;
      Invariant  : W_Pred_Id;
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
       Pred     : W_Pred_Id;
       Reason   : VC_Kind) return W_Prog_Id;
   function New_Located_Assert
      (Ada_Node : Node_Id;
       Pred     : W_Pred_Id) return W_Prog_Id;
   --  Build a named assert (in programs) of a predicate

   function New_Located_Abstract
     (Ada_Node : Node_Id;
      Expr     : W_Prog_Id;
      Post     : W_Pred_Id) return W_Prog_Id;
   --  build a located abstract Why3 program expression.

   function New_Simpl_Any_Prog
     (T    : W_Base_Type_Id;
      Pred : W_Pred_OId := Why_Empty) return W_Prog_Id;
   --  Build a "any" expression whose type is a simple type, satisfying
   --  proposition Pred.

   function Sequence (Left, Right : W_Prog_Id) return W_Prog_Id;
   --  Build a statement sequence of the two arguments, but try to minimize
   --  nesting of W_Statement_Sequence constructors.

   function Sequence (Progs : W_Prog_Array) return W_Prog_Id
   with Pre => Progs'Length /= 0;

   function New_Result
     (T : W_Base_Type_Id)
     return W_Binder_Id;

end Why.Gen.Progs;
