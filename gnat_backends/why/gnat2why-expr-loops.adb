------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                    G N A T 2 W H Y - E X P R - L O O P                   --
--                                                                          --
--                                 B o d y                                  --
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

--  For debugging, to print info on the output before raising an exception
with Ada.Text_IO;

with String_Utils;       use String_Utils;

with Atree;              use Atree;
with Sinfo;              use Sinfo;
with Snames;             use Snames;
with Uintp;              use Uintp;
with VC_Kinds;           use VC_Kinds;

with Alfa.Util;          use Alfa.Util;

with Why;                use Why;
with Why.Atree.Builders; use Why.Atree.Builders;
with Why.Atree.Tables;   use Why.Atree.Tables;
with Why.Conversions;    use Why.Conversions;
with Why.Gen.Decl;       use Why.Gen.Decl;
with Why.Gen.Expr;       use Why.Gen.Expr;
with Why.Gen.Names;      use Why.Gen.Names;
with Why.Gen.Progs;      use Why.Gen.Progs;
with Why.Gen.Preds;      use Why.Gen.Preds;
with Why.Types;          use Why.Types;
with Why.Inter;          use Why.Inter;

with Gnat2Why.Nodes;     use Gnat2Why.Nodes;
with Gnat2Why.Util;      use Gnat2Why.Util;

package body Gnat2Why.Expr.Loops is

   -----------------------
   -- Local Subprograms --
   -----------------------

   procedure Get_Loop_Invariant
     (Loop_Stmts     : List_Of_Nodes.List;
      Initial_Stmts  : out List_Of_Nodes.List;
      Loop_Invariant : out Node_Id;
      Final_Stmts    : out List_Of_Nodes.List);
   --  Loop_Stmts is a flattened list of statements and declarations in a loop
   --  body. It includes the statements and declarations that appear directly
   --  in the main list inside the loop, and recursively all inner declarations
   --  and statements that appear in block statements.
   --
   --  Get_Loop_Invariant splits this list into three buckets:
   --   * Initial_Stmts is the list of initial statements and declarations
   --     before the first occurrence of pragma Loop_Invariant;
   --   * Loop_Invariant is the node of the first occurrence of pragma
   --     Loop_Invariant in the list, if any, and Empty otherwise;
   --   * Final_Stmts is the list of final statements and declarations
   --     after the first occurrence of pragma Loop_Invariant.

   function Loop_Entity_Of_Exit_Statement (N : Node_Id) return Entity_Id;
   --  Return the Defining_Identifier of the loop that belongs to an exit
   --  statement.

   function Wrap_Loop
     (Loop_Name          : String;
      Loop_Start         : W_Prog_Id;
      Loop_End           : W_Prog_Id;
      Enter_Condition    : W_Prog_Id;
      Loop_Condition     : W_Prog_Id;
      Implicit_Invariant : W_Pred_Id;
      User_Invariant     : W_Pred_Id;
      Invariant_Check    : W_Prog_Id) return W_Prog_Id;
   --  Returns the loop expression in Why. Loop_Start and Loop_End correspond
   --  to the statements and declarations respectively before and after the
   --  loop invariant pragma put by the user, if any. Otherwise, Loop_Start is
   --  the void expression, and Loop_End corresponds to all statements in the
   --  loop. Enter_Condition and Loop_Condition are respectively the conditions
   --  for entering the loop the first time, and staying in the loop at each
   --  execution of the loop. Implicit_Invariant is the condition that can
   --  be assumed to hold at the start of the Why loop. User_Invariant is the
   --  invariant to use for the Why loop. Invariant_Check is the Why program
   --  checking that the user invariant does not raise a run-time error.
   --
   --  See comments in Wrap_Loop's body for the actual transformation.

   ------------------------
   -- Get_Loop_Invariant --
   ------------------------

   procedure Get_Loop_Invariant
     (Loop_Stmts     : List_Of_Nodes.List;
      Initial_Stmts  : out List_Of_Nodes.List;
      Loop_Invariant : out Node_Id;
      Final_Stmts    : out List_Of_Nodes.List)
   is
      Loop_Invariant_Found : Boolean := False;

   begin
      for N of Loop_Stmts loop
         if Loop_Invariant_Found then
            Final_Stmts.Append (N);

         elsif Is_Pragma_Check (N, Name_Loop_Invariant) then
            Loop_Invariant := N;
            Loop_Invariant_Found := True;

         else
            Initial_Stmts.Append (N);
         end if;
      end loop;

      if not Loop_Invariant_Found then
         Loop_Invariant := Empty;
      end if;
   end Get_Loop_Invariant;

   -----------------------------------
   -- Loop_Entity_Of_Exit_Statement --
   -----------------------------------

   function Loop_Entity_Of_Exit_Statement (N : Node_Id) return Entity_Id is
   begin
      --  If the name is directly in the given node, return that name

      if Present (Name (N)) then
         return Entity (Name (N));

      --  Otherwise the exit statement belongs to the innermost loop, so
      --  simply go upwards (follow parent nodes) until we encounter the
      --  loop

      else
         declare
            Cur_Node : Node_Id := N;
         begin
            while Nkind (Cur_Node) /= N_Loop_Statement loop
               Cur_Node := Parent (Cur_Node);
            end loop;
            return Entity (Identifier (Cur_Node));
         end;
      end if;
   end Loop_Entity_Of_Exit_Statement;

   ------------------------------
   -- Transform_Exit_Statement --
   ------------------------------

   function Transform_Exit_Statement (Stmt : Node_Id) return W_Prog_Id
   is
      Loop_Entity : constant Entity_Id := Loop_Entity_Of_Exit_Statement (Stmt);
      Exc_Name    : constant String :=
        Capitalize_First (Full_Name (Loop_Entity));
      Raise_Stmt  : constant W_Prog_Id :=
                      New_Raise
                        (Ada_Node => Stmt,
                         Name => New_Identifier (Name => Exc_Name));
   begin
      if Nkind (Condition (Stmt)) = N_Empty then
         return Raise_Stmt;
      else
         return
           New_Conditional
             (Ada_Node  => Stmt,
              Condition => +Transform_Expr (Condition (Stmt),
                                            EW_Bool_Type,
                                            EW_Prog,
                                            Params => Body_Params),
              Then_Part => +Raise_Stmt);
      end if;
   end Transform_Exit_Statement;

   ------------------------------
   -- Transform_Loop_Statement --
   ------------------------------

   function Transform_Loop_Statement (Stmt : Node_Id) return W_Prog_Id is
      Loop_Body   : constant List_Id   := Statements (Stmt);
      Scheme      : constant Node_Id   := Iteration_Scheme (Stmt);
      Loop_Entity : constant Entity_Id := Entity (Identifier (Stmt));
      Loop_Name   : constant String    := Full_Name (Loop_Entity);

      Loop_Stmts     : List_Of_Nodes.List;
      Initial_Stmts  : List_Of_Nodes.List;
      Final_Stmts    : List_Of_Nodes.List;
      Loop_Invariant : Node_Id;

      Initial_Prog : W_Prog_Id;
      Final_Prog   : W_Prog_Id;
      Inv_Check    : W_Prog_Id;
      Invariant    : W_Pred_Id;

   begin
      --  Retrieve the different parts of the loop

      Loop_Stmts := Get_Flat_Statement_List (Loop_Body);
      Get_Loop_Invariant
        (Loop_Stmts, Initial_Stmts, Loop_Invariant, Final_Stmts);

      --  Transform each part of the loop

      Initial_Prog := Transform_Statements (Initial_Stmts);
      Final_Prog := Transform_Statements (Final_Stmts);

      if Present (Loop_Invariant) then
         Transform_Pragma_Check (Loop_Invariant, Inv_Check, Invariant);
      else
         Inv_Check := New_Void;
         Invariant := True_Pred;
      end if;

      Invariant :=
        +New_VC_Expr
          (Ada_Node => Loop_Invariant,
           Expr     => +Invariant,
           Reason   => VC_Loop_Invariant,
           Domain   => EW_Pred);

      --  Depending on the form of the loop, put together the generated Why
      --  nodes in a different way.

      --  Case of a simple loop

      if Nkind (Scheme) = N_Empty then
         return Wrap_Loop (Loop_Name          => Loop_Name,
                           Loop_Start         => Initial_Prog,
                           Loop_End           => Final_Prog,
                           Enter_Condition    => True_Prog,
                           Loop_Condition     => True_Prog,
                           Implicit_Invariant => True_Pred,
                           User_Invariant     => Invariant,
                           Invariant_Check    => Inv_Check);

      --  Case of a WHILE loop

      elsif Nkind (Iterator_Specification (Scheme)) = N_Empty
              and then
            Nkind (Loop_Parameter_Specification (Scheme)) = N_Empty
      then
         While_Loop : declare
            Cond_Prog : constant W_Prog_Id :=
              +Transform_Expr_With_Actions (Condition (Scheme),
                                            Condition_Actions (Scheme),
                                            EW_Bool_Type,
                                            EW_Prog,
                                            Params => Body_Params);
            Cond_Pred : constant W_Pred_Id :=
              +Transform_Expr_With_Actions (Condition (Scheme),
                                            Condition_Actions (Scheme),
                                            EW_Pred,
                                            Params => Body_Params);

            --  If the Loop_Assertion pragma comes first in the loop body
            --  (possibly inside nested block statements), then we can use the
            --  loop condition as an implicit invariant of the generated Why
            --  loop. In other cases, we cannot, as this would not be always
            --  correct.

            Impl_Pred : constant W_Pred_Id :=
              (if Get_Kind (+Initial_Prog) = W_Void then
                 Cond_Pred
               else
                 True_Pred);
         begin
            return Wrap_Loop (Loop_Name          => Loop_Name,
                              Loop_Start         => Initial_Prog,
                              Loop_End           => Final_Prog,
                              Enter_Condition    => Cond_Prog,
                              Loop_Condition     => Cond_Prog,
                              Implicit_Invariant => Impl_Pred,
                              User_Invariant     => Invariant,
                              Invariant_Check    => Inv_Check);
         end While_Loop;

      --  Case of a FOR loop

      --  Here, we set the condition to express that the index is in the range
      --  of the loop. We need to evaluate the range expression once at the
      --  beginning of the loop, to get potential checks in that expression
      --  only once.

      elsif Nkind (Condition (Scheme)) = N_Empty then
         For_Loop : declare
            LParam_Spec  : constant Node_Id :=
                             Loop_Parameter_Specification (Scheme);
            Loop_Range   : constant Node_Id :=
              Discrete_Subtype_Definition (LParam_Spec);
            Ent          : constant Entity_Id :=
              Defining_Identifier (LParam_Spec);
            Is_Reverse   : constant Boolean := Reverse_Present (LParam_Spec);
            Loop_Index   : constant W_Identifier_Id :=
              New_Identifier
                (Ada_Node => Etype (Ent),
                 Name => Full_Name (Ent));
            Index_Deref  : constant W_Prog_Id :=
                             New_Deref
                               (Ada_Node => Stmt,
                                Right    => +Loop_Index);
            Update_Op    : constant EW_Binary_Op :=
                             (if Is_Reverse then EW_Substract
                              else EW_Add);
            Update_Expr  : constant W_Prog_Id :=
                             New_Binary_Op
                               (Ada_Node => Stmt,
                                Op       => Update_Op,
                                Op_Type  => EW_Int,
                                Left     => +Index_Deref,
                                Right    =>
                                  New_Integer_Constant
                                    (Ada_Node => Stmt,
                                     Value     => Uint_1));
            Update_Stmt  : constant W_Prog_Id :=
                             New_Assignment
                               (Ada_Node => Stmt,
                                Name     => Loop_Index,
                                Value    => Update_Expr);

            --  In the range expression of the invariant, explicitly
            --  set T_Type to handle the special case of
            --  Standard.Boolean, where bounds and index are of
            --  different base types (bool for bounds, int for index).

            Cond_Pred    : constant W_Pred_Id :=
              +Range_Expr (Loop_Range,
                           New_Deref (Right => Loop_Index),
                           EW_Pred,
                           Params => Body_Params,
                           T_Type => EW_Int_Type);
            Actual_Range : constant Node_Id := Get_Range (Loop_Range);
            Low_Ident    : constant W_Identifier_Id := New_Temp_Identifier;
            High_Ident   : constant W_Identifier_Id := New_Temp_Identifier;
            Init_Index   : constant W_Identifier_Id :=
              (if Is_Reverse then High_Ident else Low_Ident);
            Exit_Index   : constant W_Identifier_Id :=
              (if Is_Reverse then Low_Ident else High_Ident);
            Exit_Cmp     : constant EW_Relation :=
              (if Is_Reverse then EW_Ge else EW_Le);
            Exit_Cond    : constant W_Expr_Id :=
              New_Relation (Domain  => EW_Prog,
                            Op_Type => EW_Int,
                            Op      => Exit_Cmp,
                            Left    => +Index_Deref,
                            Right   => +Exit_Index);
            Cond_Prog    : constant W_Prog_Id :=
              +New_Range_Expr (Domain    => EW_Prog,
                               Base_Type => EW_Int_Type,
                               Low       => +Low_Ident,
                               High      => +High_Ident,
                               Expr      => +Index_Deref);
            Entire_Loop  : W_Prog_Id :=
              Wrap_Loop (Loop_Name          => Loop_Name,
                         Loop_Start         => Initial_Prog,
                         Loop_End           =>
                           Sequence (Final_Prog, Update_Stmt),
                         Enter_Condition    => Cond_Prog,
                         Loop_Condition     => +Exit_Cond,
                         Implicit_Invariant => Cond_Pred,
                         User_Invariant     => Invariant,
                         Invariant_Check    => Inv_Check);

         --  Start of For_Loop

         begin
            Entire_Loop := New_Binding_Ref
                             (Name    => Loop_Index,
                              Def     => +Init_Index,
                              Context => Entire_Loop);
            Entire_Loop :=
               New_Binding
                 (Name    => High_Ident,
                  Def     => +Transform_Expr (High_Bound (Actual_Range),
                                              EW_Int_Type,
                                              EW_Prog,
                                              Params => Body_Params),
                  Context => +Entire_Loop);
            Entire_Loop :=
               New_Binding
                 (Name    => Low_Ident,
                  Def     => +Transform_Expr (Low_Bound (Actual_Range),
                                              EW_Int_Type,
                                              EW_Prog,
                                              Params => Body_Params),
                  Context => +Entire_Loop);
            return
              Sequence
                (Assume_Of_Subtype_Indication (Body_Params, Loop_Range),
                 Entire_Loop);
         end For_Loop;

      else
         --  Some other kind of loop
         Ada.Text_IO.Put_Line ("[Transform_Loop_Statement] other loop");
         raise Not_Implemented;
      end if;
   end Transform_Loop_Statement;

   ---------------
   -- Wrap_Loop --
   ---------------

   --  Generate the following Why loop expression:
   --
   --  if enter_condition then
   --    loop_start;
   --    invariant_check;
   --    try
   --      loop invariant { user_invariant }
   --         assume { implicit_invariant };
   --         loop_end;
   --         if loop_condition then
   --            loop_start;
   --            invariant_check
   --         else raise loop_name
   --      end loop
   --    with loop_name -> void
   --  end if

   function Wrap_Loop
     (Loop_Name          : String;
      Loop_Start         : W_Prog_Id;
      Loop_End           : W_Prog_Id;
      Enter_Condition    : W_Prog_Id;
      Loop_Condition     : W_Prog_Id;
      Implicit_Invariant : W_Pred_Id;
      User_Invariant     : W_Pred_Id;
      Invariant_Check    : W_Prog_Id) return W_Prog_Id
   is
      Loop_Ident : constant W_Identifier_Id :=
        New_Identifier (Name => Capitalize_First (Loop_Name));

      Loop_Body : constant W_Prog_Id :=
        Sequence
          (New_Assume_Statement
             (Ada_Node => Empty, Post => Implicit_Invariant),
           Sequence
             (Loop_End,
              New_Conditional
                (Condition => +Loop_Condition,
                 Then_Part => +Sequence (Loop_Start, Invariant_Check),
                 Else_Part => New_Raise (Name => Loop_Ident))));

      Loop_Stmt : constant W_Prog_Id :=
        New_While_Loop
          (Condition    => True_Prog,
           Annotation   => New_Loop_Annot (Invariant => User_Invariant),
           Loop_Content => Loop_Body);

      Loop_Try : constant W_Prog_Id :=
        New_Try_Block
          (Prog    => Loop_Stmt,
           Handler => (1 => New_Handler (Name => Loop_Ident,
                                         Def  => New_Void)));

   begin
      Emit (Body_Params.Theory,
            New_Exception_Declaration (Name => Loop_Ident, Arg  => Why_Empty));

      return
        New_Conditional
          (Condition => +Enter_Condition,
           Then_Part => +Sequence ((Loop_Start, Invariant_Check, Loop_Try)));
   end Wrap_Loop;

end Gnat2Why.Expr.Loops;
