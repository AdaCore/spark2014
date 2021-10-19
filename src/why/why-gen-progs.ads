------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                        W H Y - G E N - P R O G S                         --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                     Copyright (C) 2010-2021, AdaCore                     --
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

with SPARK_Util;                use SPARK_Util;
with Types;                     use Types;
with VC_Kinds;                  use VC_Kinds;
with SPARK_Atree;               use SPARK_Atree;
with Why.Atree.Builders;        use Why.Atree.Builders;
with Why.Atree.Modules;         use Why.Atree.Modules;
with Why.Conversions;           use Why.Conversions;
with Why.Gen.Expr;              use Why.Gen.Expr;
with Why.Ids;                   use Why.Ids;
with Why.Sinfo;                 use Why.Sinfo;
with Why.Types;                 use Why.Types;

package Why.Gen.Progs is

   True_Prog  : constant W_Prog_Id := New_Literal (Value => EW_True);
   False_Prog : constant W_Prog_Id := New_Literal (Value => EW_False);

   ----------------------------------------------------------------------------
   --  Creating sequences of statements in Why3 can be done in multiple ways,
   --  depending on the types of nodes involved:
   --
   --  * functions Sequence return a new sequence node based on their
   --    arguments, optimizing out the Void statements
   --  * procedures Append update their first argument by creating a new
   --    sequence node chaining all arguments (obtained by calling Sequence)
   --  * procedures Prepend update their last argument by creating a new
   --    sequence node chaining all arguments (obtained by calling Sequence)
   --
   --  Procedures Append/Prepend that operate on types W_Prog_Id and W_Expr_Id
   --  (which should also be program nodes, only with more general type
   --  W_Expr_Id) do not mutate their input values. A new node is created if
   --  needed, and the first/last parameter is updated to refer to this node.
   --
   --  Procedures Append/Prepend that operate on type W_Statement_Sequence_Id
   --  on the contrary directly mutate the underlying Why3 node. This is an
   --  optimization for cases where there is a risk of creating too deep Why3
   --  programs, which causes scalabilty issues. The mutated parameter is of
   --  mode IN OUT to clearly signal to callers that the argument is mutated.
   --  Note that this should only be applied when the node is not already
   --  shared in the AST, otherwise the changes apply to all subtrees that
   --  include it.
   ----------------------------------------------------------------------------

   pragma Annotate (Xcov, Exempt_On, "Ghost code");
   function Has_Empty_Or_Unit_Type (Prog : W_Prog_Id) return Boolean is
     (Get_Type (+Prog) = Why_Empty
      or else Get_Type (+Prog) = EW_Unit_Type)
   with Ghost;
   pragma Annotate (Xcov, Exempt_Off);

   procedure Append
     (Left  : in out W_Prog_Id;
      Right : W_Prog_Id)
   with Pre => Has_Empty_Or_Unit_Type (Left);

   procedure Append
     (Left           : in out W_Prog_Id;
      Right1, Right2 : W_Prog_Id)
   with Pre => Has_Empty_Or_Unit_Type (Left)
     and then Has_Empty_Or_Unit_Type (Right1);

   procedure Append
     (Left  : in out W_Expr_Id;
      Right : W_Prog_Id)
   with Pre => Has_Empty_Or_Unit_Type (+Left);

   procedure Append
     (Left           : in out W_Expr_Id;
      Right1, Right2 : W_Prog_Id)
   with Pre => Has_Empty_Or_Unit_Type (+Left)
     and then Has_Empty_Or_Unit_Type (Right1);

   procedure Append
     (Left  : in out W_Statement_Sequence_Id;
      Right : W_Statement_Sequence_Id);

   procedure Append
     (Left : in out W_Statement_Sequence_Id;
      Right : W_Prog_Id);

   procedure Emit_Always_True_Range_Check
     (Ada_Node   : Node_Id;
      Check_Kind : Scalar_Check_Kind);

   function New_Any_Statement
     (Ada_Node    : Node_Id := Empty;
      Post        : W_Pred_Id;
      Return_Type : W_Type_Id := Why_Empty)
      return W_Prog_Id;
   --  Generate a node of the form "any type requires ensures {post}"
   --  Such a node in Why is a bit like a function call with post and
   --  return type, but can be used at any place.
   --  @param Ada_Node Ada_Node used for the any node
   --  @param Post the postcondition used for the any statement
   --  @param Return_Type the type used for the any statement
   --  @return an any node

   function New_Any_Statement
     (Ada_Node    : Node_Id;
      Pre         : W_Pred_Id;
      Post        : W_Pred_Id;
      Reason      : VC_Kind;
      Return_Type : W_Type_Id := Why_Empty)
      return W_Prog_Id
   with Pre => Present (Ada_Node);
   --  Generate a node of the form "any type requires {pre} ensures {post}"
   --  Same as above except that a VC will be generated for the precondition
   --  so a reason and an Ada node should be provided.
   --  @param Ada_Node Ada_Node used for the any node
   --  @param Pre the precondition used for the any statement
   --  @param Post the postcondition used for the any statement
   --  @param Return_Type the type used for the any statement
   --  @return an any node

   function New_Assume_Statement
     (Ada_Node : Node_Id := Empty;
      Pred     : W_Pred_Id)
     return W_Prog_Id;
   --  generate an assume statement, which inserts a hypothesis in the context
   --  @param Ada_Node Ada_Node used for the assume node
   --  @param Pred the predicate which will be inserted in the context
   --  @return an assume statement

   function New_Havoc_Statement
     (Ada_Node : Node_Id := Empty;
      Effects  : W_Effects_Id) return W_Prog_Id;

   function New_Ignore (Ada_Node : Node_Id := Empty; Prog : W_Prog_Id)
      return W_Prog_Id;
   --   Build the program "ignore(prog)" of return type "unit".

   function New_Located_Assert
      (Ada_Node : Node_Id;
       Pred     : W_Pred_Id;
       Reason   : VC_Kind;
       Kind     : EW_Assert_Kind;
       Info     : Check_Info := (others => <>)) return W_Prog_Id;

   function New_Located_Abstract
     (Ada_Node : Node_Id;
      Expr     : W_Prog_Id;
      Post     : W_Pred_Id;
      Reason   : VC_Kind)
      return W_Prog_Id;
   --  build a located abstract Why3 program expression with a postcondition.

   function New_Simpl_Any_Prog
     (T    : W_Type_Id;
      Pred : W_Pred_OId := Why_Empty) return W_Prog_Id;
   --  Build a "any" expression whose type is a simple type, satisfying
   --  proposition Pred.

   procedure Prepend
     (Left  : W_Prog_Id;
      Right : in out W_Prog_Id)
   with Pre => Has_Empty_Or_Unit_Type (Left);

   procedure Prepend
     (Left  : W_Prog_Id;
      Right : in out W_Expr_Id)
   with Pre => Has_Empty_Or_Unit_Type (Left);

   procedure Prepend
     (Left1, Left2  : W_Prog_Id;
      Right         : in out W_Prog_Id)
   with Pre => Has_Empty_Or_Unit_Type (Left1)
     and then Has_Empty_Or_Unit_Type (Left2);

   procedure Prepend
     (Left1, Left2  : W_Prog_Id;
      Right         : in out W_Expr_Id)
   with Pre => Has_Empty_Or_Unit_Type (Left1)
     and then Has_Empty_Or_Unit_Type (Left2);

   procedure Prepend
     (Left  : W_Statement_Sequence_Id;
      Right : in out W_Statement_Sequence_Id);

   procedure Prepend
     (Left  : W_Prog_Id;
      Right : in out W_Statement_Sequence_Id)
   with Pre => Has_Empty_Or_Unit_Type (Left);

   function Sequence
     (Ada_Node    : Node_Id;
      Left, Right : W_Prog_Id)
      return W_Prog_Id
   with Pre => Has_Empty_Or_Unit_Type (Left);

   function Sequence (Left, Right : W_Prog_Id) return W_Prog_Id is
     (Sequence (Empty, Left, Right))
   with Pre => Has_Empty_Or_Unit_Type (Left);

   function Sequence (Progs : W_Prog_Array) return W_Prog_Id
   with Pre => Progs'Length /= 0;

end Why.Gen.Progs;
