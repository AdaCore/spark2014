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
with Namet;              use Namet;
with Nlists;             use Nlists;
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
      Loop_Variant   : out Node_Id;
      Final_Stmts    : out List_Of_Nodes.List);
   --  Loop_Stmts is a flattened list of statements and declarations in a loop
   --  body. It includes the statements and declarations that appear directly
   --  in the main list inside the loop, and recursively all inner declarations
   --  and statements that appear in block statements.
   --
   --  Get_Loop_Invariant splits this list into four buckets:
   --   * Initial_Stmts is the list of initial statements and declarations
   --     before the first occurrence of pragma Loop_Invariant, or the empty
   --     list if there are no pragma Loop_Invariant in the loop.
   --   * Loop_Invariant is the node of the first occurrence of pragma
   --     Loop_Invariant in the list, if any, and Empty otherwise.
   --   * Loop_Variant is the node of the pragma Loop_Variant just after
   --     Loop_Invariant (without intermediate statements), if any;
   --     or otherwise the node of the pragma Loop_Variant just before
   --     Loop_Invariant (without intermediate statements), if any;
   --     and Empty otherwise. Note that Initial_Stmts and Final_Stmts do not
   --     contain Loop_Variant if it is not Empty.
   --   * Final_Stmts is the list of final statements and declarations
   --     after the first occurrence of pragma Loop_Invariant, or all the
   --     statements of the loop if there are no pragma Loop_Invariant in the
   --     loop.

   function Loop_Entity_Of_Exit_Statement (N : Node_Id) return Entity_Id;
   --  Return the Defining_Identifier of the loop that belongs to an exit
   --  statement.

   procedure Transform_Loop_Variant
     (Stmt       : Node_Id;
      Check_Part : out W_Prog_Id;
      Logic_Part : out W_Pred_Id;
      Tmp_Vars   : out W_Identifier_List;
      Tmp_Assign : out W_Assignment_List);
   --  Given a pragma Loop_Variant in Stmt, returns the Why node for checking
   --  that a loop variant does not raise run-time errors in Check_Part, and
   --  the Why node for the logic proposition that the variant increases or
   --  decreases as desired in Logic_Part. Tmp_Assign is a list of assignments
   --  of expression nodes in the loop variant to temporary names used to refer
   --  to their saved values, returned in Tmp_Vars.

   function Wrap_Loop
     (Loop_Name          : String;
      Loop_Start         : W_Prog_Id;
      Loop_End           : W_Prog_Id;
      Enter_Condition    : W_Prog_Id;
      Loop_Condition     : W_Prog_Id;
      Implicit_Invariant : W_Pred_Id;
      User_Invariant     : W_Pred_Id;
      Invariant_Check    : W_Prog_Id;
      Variant_Tmps       : W_Identifier_List;
      Variant_Update     : W_Prog_Id;
      Variant_Check      : W_Prog_Id) return W_Prog_Id;
   --  Returns the loop expression in Why.
   --
   --  Loop_Start and Loop_End correspond to the statements and declarations
   --  respectively before and after the loop invariant pragma put by the
   --  user, if any. Otherwise, Loop_Start is the void expression, and
   --  Loop_End corresponds to all statements in the loop.
   --
   --  Enter_Condition and Loop_Condition are respectively the conditions
   --  for entering the loop the first time, and staying in the loop at
   --  each execution of the loop.
   --
   --  Implicit_Invariant is the condition that can be assumed to hold at the
   --  start of the Why loop. User_Invariant is the invariant to use for the
   --  Why loop. Invariant_Check is the Why program checking that the user
   --  invariant does not raise a run-time error.
   --
   --  Variant_Tmps is the list of temporary identifiers used to save the value
   --  of the loop variant expressions. Variant_Update assigns the current
   --  value of the loop variant expressions to these temporary variables.
   --  Variant_Check checks both the absence of run-time errors in the loop
   --  variant, and that the loop variant makes progress.
   --
   --  See comments in Wrap_Loop's body for the actual transformation.

   ------------------------
   -- Get_Loop_Invariant --
   ------------------------

   procedure Get_Loop_Invariant
     (Loop_Stmts     : List_Of_Nodes.List;
      Initial_Stmts  : out List_Of_Nodes.List;
      Loop_Invariant : out Node_Id;
      Loop_Variant   : out Node_Id;
      Final_Stmts    : out List_Of_Nodes.List)
   is
      Loop_Invariant_Found : Boolean := False;
      N : Node_Id;

      use List_Of_Nodes;

   begin
      Loop_Invariant := Empty;
      Loop_Variant   := Empty;

      for Cur in Loop_Stmts.Iterate loop
         N := Element (Cur);

         --  If this is the first pragma Loop_Invariant, mark it as the
         --  official loop invariant.

         if not Loop_Invariant_Found
           and then Is_Pragma_Check (N, Name_Loop_Invariant)
         then
            Loop_Invariant := N;
            Loop_Invariant_Found := True;

         --  If this is a pragma Loop_Variant preceding or following the
         --  official loop invariant, mark it as the official loop variant.
         --  If there are both a pragma Loop_Variant preceding and following
         --  the official loop invariant, choose the one following the loop
         --  invariant as the official loop variant.

         elsif Is_Pragma (N, Pragma_Loop_Variant)
           and then

             --  Case where the Loop_Variant follows the official loop
             --  invariant.

             ((Loop_Invariant_Found
                 and then
               Element (Previous (Cur)) = Loop_Invariant)

                 or else

              --  Case where the Loop_Variant precedes the official loop
              --  invariant, and there are no following Loop_Variant.

              (not Loop_Invariant_Found
                 and then
               Present (Element (Next (Cur)))
                 and then
               Is_Pragma_Check (Element (Next (Cur)), Name_Loop_Invariant)
                 and then
               (not (Present (Element (Next (Next (Cur))))
                      and then
                     Is_Pragma (Element (Next (Next (Cur))),
                                Pragma_Loop_Variant)))))
         then
            Loop_Variant := N;

         elsif Loop_Invariant_Found then
            Final_Stmts.Append (N);

         else
            Initial_Stmts.Append (N);
         end if;
      end loop;

      --  If not loop invariant was found, put all statements and declarations
      --  in the list Final_Stmts, leaving the list Initial_Stmts empty.

      if not Loop_Invariant_Found then
         Final_Stmts.Move (Initial_Stmts);
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
      Loop_Variant   : Node_Id;

      Initial_Prog   : W_Prog_Id;
      Final_Prog     : W_Prog_Id;

      --  Variables for the loop invariant, default initialized to the proper
      --  values when the loop does not have an invariant.

      Inv_Check      : W_Prog_Id := New_Void;
      Invariant      : W_Pred_Id := True_Pred;

      --  Variables for the loop variant, default initialized to the proper
      --  values when the loop does not have a variant.

      Variant_Check  : W_Prog_Id := New_Void;
      Variant_Update : W_Prog_Id := New_Void;
      Variant_Tmps   : W_Identifier_List :=
        W_Identifier_List (Why.Atree.Tables.New_List);

   begin
      --  Retrieve the different parts of the loop

      Loop_Stmts := Get_Flat_Statement_List (Loop_Body);
      Get_Loop_Invariant
        (Loop_Stmts, Initial_Stmts, Loop_Invariant, Loop_Variant, Final_Stmts);

      --  Transform statements before and after the loop invariant

      Initial_Prog := Transform_Statements (Initial_Stmts);
      Final_Prog := Transform_Statements (Final_Stmts);

      --  Generate the relevant bits for the loop invariant if present

      if Present (Loop_Invariant) then
         Transform_Pragma_Check (Loop_Invariant, Inv_Check, Invariant);
      end if;

      --  ??? Do we always want to generate a loop invariant, even when there
      --  are no Loop_Invariant pragmas in the loop?

      Invariant :=
        +New_VC_Expr
          (Ada_Node => Loop_Invariant,
           Expr     => +Invariant,
           Reason   => VC_Loop_Invariant,
           Domain   => EW_Pred);

      --  Generate the relevant bits for the loop variant if present

      if Present (Loop_Variant) then
         declare
            Variant_Prog : W_Prog_Id;
            Variant_Pred : W_Pred_Id;
            Tmp_Assign   : W_Assignment_List;
            Variant_Init : Node_Lists.List;

         begin
            --  Generate the Why expressions for checking absence of run-time
            --  errors and variant progress.

            Transform_Loop_Variant (Stmt       => Loop_Variant,
                                    Check_Part => Variant_Prog,
                                    Logic_Part => Variant_Pred,
                                    Tmp_Vars   => Variant_Tmps,
                                    Tmp_Assign => Tmp_Assign);

            --  Create a VC for the loop variant

            Variant_Pred := +New_VC_Expr (Ada_Node => Loop_Variant,
                                          Expr     => +Variant_Pred,
                                          Reason   => VC_Loop_Variant,
                                          Domain   => EW_Pred);

            --  Retrieve the list of assignments to save variant expressions

            Variant_Init := Get_List (+Tmp_Assign);

            declare
               Variant_Assign : W_Prog_Array (1 ..
                                              Positive (Variant_Init.Length));
               J : Positive := 1;
            begin
               for Assign of Variant_Init loop
                  Variant_Assign (J) := +Assign;
                  J := J + 1;
               end loop;

               --  Create the program that updates the variables holding saved
               --  values of variant expressions.

               Variant_Update := Sequence (Variant_Assign);

               --  Combine the run-time check and the loop variant check in
               --  one program Variant_Check, for use in Loop_Wrap.

               Variant_Check :=
                 Sequence (New_Ignore (Prog => Variant_Prog),
                           New_Located_Assert (Ada_Node => Loop_Variant,
                                               Pred     => Variant_Pred));
            end;
         end;
      end if;

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
                           Invariant_Check    => Inv_Check,
                           Variant_Tmps       => Variant_Tmps,
                           Variant_Update     => Variant_Update,
                           Variant_Check      => Variant_Check);

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
                              Invariant_Check    => Inv_Check,
                              Variant_Tmps       => Variant_Tmps,
                              Variant_Update     => Variant_Update,
                              Variant_Check      => Variant_Check);
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
                         Invariant_Check    => Inv_Check,
                         Variant_Tmps       => Variant_Tmps,
                         Variant_Update     => Variant_Update,
                         Variant_Check      => Variant_Check);

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

   ----------------------------
   -- Transform_Loop_Variant --
   ----------------------------

   --  Given a pragma Loop_Variant of the form:

   --    pragma Loop_Variant (Dir1 => Expr1,
   --                         Dir2 => Expr2,
   --                             ...
   --                         Dirn => Exprn);

   --  Generates a Why program Check_Part of the form:

   --    ignore (expr1);
   --    if expr1 = sav1 then
   --       (ignore (expr2);
   --        if expr2 = sav2 then
   --          ...
   --          ignore (exprn));

   --  where sav1, sav2 ... savn are the saved values of expr1, expr2 ... exprn
   --  at the start of each loop run, and at the point of occurrence of the
   --  loop variant. These names are returned in the list Tmp_Vars.

   --  and a Why proposition Logic_Part of the form:

   --    expr1 op1 sav1 or (expr1 = sav1 and
   --                       expr2 op2 sav2 or (expr2 = sav2 and
   --                                          ...
   --                                          exprn opn savn))

   --  where op1, op2 ... opn is the operator < when the variant part is
   --  decreasing, and > when the variant part is increasing.

   --  Tmp_Assign is simply the list of assignments:

   --    sav1 := expr1;
   --    sav2 := expr2;
   --        ...
   --    savn := exprn

   procedure Transform_Loop_Variant
     (Stmt       : Node_Id;
      Check_Part : out W_Prog_Id;
      Logic_Part : out W_Pred_Id;
      Tmp_Vars   : out W_Identifier_List;
      Tmp_Assign : out W_Assignment_List)
   is
      Variant : Node_Id;

      function Variant_Expr
        (Expr   : Node_Id;
         Domain : EW_Domain) return W_Expr_Id;
      --  Returns the value of the variant expression Expr as an int

      function Variant_Part_Does_Progress
        (Variant : Node_Id;
         Name    : W_Identifier_Id) return W_Pred_Id;
      --  Given a node Variant corresponding to a decreasing or increasing
      --  part in a loop variant, and a name Name to designate that expression,
      --  returns the Why term that corresponds to progress.

      function Variant_Part_Stays_Constant
        (Variant : Node_Id;
         Name    : W_Identifier_Id) return W_Pred_Id;
      --  Given a node Variant corresponding to a decreasing or increasing
      --  part in a loop variant, and a name Name to designate that expression,
      --  returns the Why term that expresses that it has not been modified.

      ------------------
      -- Variant_Expr --
      ------------------

      function Variant_Expr
        (Expr   : Node_Id;
         Domain : EW_Domain) return W_Expr_Id
      is
         Params : constant Transformation_Params :=
           (if Domain = EW_Prog then Body_Params else Assert_Params);
      begin
         return Transform_Expr (Expr          => Expr,
                                Expected_Type => EW_Int_Type,
                                Domain        => Domain,
                                Params        => Params);
      end Variant_Expr;

      --------------------------------
      -- Variant_Part_Does_Progress --
      --------------------------------

      function Variant_Part_Does_Progress
        (Variant : Node_Id;
         Name    : W_Identifier_Id) return W_Pred_Id
      is
         Expr : constant Node_Id := Expression (Variant);
         Cmp  : constant EW_Relation :=
           (if Chars (Variant) = Name_Decreases then EW_Lt else EW_Gt);
      begin
         return +New_Comparison (Cmp       => Cmp,
                                 Left      => Variant_Expr (Expr, EW_Term),
                                 Right     => New_Deref (Right => +Name),
                                 Arg_Types => EW_Int_Type,
                                 Domain    => EW_Pred);
      end Variant_Part_Does_Progress;

      ---------------------------------
      -- Variant_Part_Stays_Constant --
      ---------------------------------

      function Variant_Part_Stays_Constant
        (Variant : Node_Id;
         Name    : W_Identifier_Id) return W_Pred_Id
      is
         Expr : constant Node_Id := Expression (Variant);
      begin
         return +New_Comparison (Cmp       => EW_Eq,
                                 Left      => Variant_Expr (Expr, EW_Term),
                                 Right     => New_Deref (Right => +Name),
                                 Arg_Types => EW_Int_Type,
                                 Domain    => EW_Pred);
      end Variant_Part_Stays_Constant;

   --  Start of Transform_Loop_Variant

   begin
      --  Unused initialization to avoid compiler warning that variable may be
      --  used before being assigned to.

      Check_Part := New_Void;
      Logic_Part := True_Pred;

      --  Force initialization because the caller does not ncessarily
      --  initialize the lists.

      Tmp_Vars := W_Identifier_List (Why.Atree.Tables.New_List);
      Tmp_Assign := W_Assignment_List (Why.Atree.Tables.New_List);

      --  Build incrementally Check_Part and Logic_Part, assuming these
      --  variables already contain the Why nodes created for the variant
      --  cases that follow this one.

      --  Create a new name to designate the expression that is increasing or
      --  decreasing, and update Tmp_Vars and Tmp_Assign accordingly.

      Variant := Last (Pragma_Argument_Associations (Stmt));
      while Present (Variant) loop
         declare
            Name : constant W_Identifier_Id := New_Temp_Identifier;
            Expr : constant Node_Id := Expression (Variant);

            Pred_Progress : constant W_Pred_Id :=
              Variant_Part_Does_Progress (Variant, Name);
            Pred_Constant : constant W_Pred_Id :=
              Variant_Part_Stays_Constant (Variant, Name);
            Prog : constant W_Prog_Id :=
              New_Ignore (Prog => +Variant_Expr (Expr, EW_Prog));
            Assign : constant W_Assignment_Id :=
              New_Assignment (Name  => Name,
                              Value => +Variant_Expr (Expr, EW_Term));

         begin
            Append (Why_Node_List (Tmp_Vars), +Name);
            Append (Why_Node_List (Tmp_Assign), +Assign);

            Check_Part :=
              (if No (Next (Variant)) then
                 Prog
               else
                 Sequence (Prog,
                   +W_Expr_Id'(New_Conditional (Ada_Node    => Variant,
                                                Domain      => EW_Prog,
                                                Condition   => +Pred_Progress,
                                                Then_Part   => +Check_Part))));

            Logic_Part :=
              (if No (Next (Variant)) then
                 Pred_Progress
               else
                 +New_Or_Expr (Left   => +Pred_Progress,
                               Right  => New_And_Expr
                                           (Left   => +Pred_Constant,
                                            Right  => +Logic_Part,
                                            Domain => EW_Pred),
                               Domain => EW_Pred));
         end;

         Prev (Variant);
      end loop;
   end Transform_Loop_Variant;

   ---------------
   -- Wrap_Loop --
   ---------------

   --  Generate the following Why loop expression:
   --
   --  if enter_condition then
   --    try
   --      loop_start;
   --      loop invariant { user_invariant }
   --         assume { implicit_invariant };
   --         invariant_check;
   --         let variant_tmps = ref 0 in
   --            variant_update;
   --            loop_end;
   --            if loop_condition then
   --               loop_start;
   --               variant_check
   --            else
   --               raise loop_name
   --      end loop
   --    with loop_name -> void
   --  end if
   --
   --  Note that the expression that checks that the user invariant does not
   --  raise a run-time error (invariant_check) is put inside the loop, in a
   --  context where the user invariant and the implicit invariant are known to
   --  hold. A naive translation would put it after the two copies of
   --  loop_start, but it is more efficient to put it in only one place. Both
   --  choices are logically equivalent, because the user invariant must be
   --  proved before it can be used in the loop.

   function Wrap_Loop
     (Loop_Name          : String;
      Loop_Start         : W_Prog_Id;
      Loop_End           : W_Prog_Id;
      Enter_Condition    : W_Prog_Id;
      Loop_Condition     : W_Prog_Id;
      Implicit_Invariant : W_Pred_Id;
      User_Invariant     : W_Pred_Id;
      Invariant_Check    : W_Prog_Id;
      Variant_Tmps       : W_Identifier_List;
      Variant_Update     : W_Prog_Id;
      Variant_Check      : W_Prog_Id) return W_Prog_Id
   is
      Loop_Ident : constant W_Identifier_Id :=
        New_Identifier (Name => Capitalize_First (Loop_Name));

      Loop_Inner : constant W_Prog_Id :=
        Create_Zero_Binding
          (Vars => Variant_Tmps,
           Prog => Sequence
             ((1 => Variant_Update,
               2 => Loop_End,
               3 => New_Conditional
                 (Condition => +Loop_Condition,
                  Then_Part => +Sequence (+Loop_Start, +Variant_Check),
                  Else_Part => New_Raise (Name => Loop_Ident)))));

      Loop_Body : constant W_Prog_Id :=
        Sequence ((1 => New_Assume_Statement
                          (Ada_Node => Empty, Post => Implicit_Invariant),
                   2 => Invariant_Check,
                   3 => Loop_Inner));

      Loop_Stmt : constant W_Prog_Id :=
        New_While_Loop
          (Condition    => True_Prog,
           Annotation   => New_Loop_Annot (Invariant => User_Invariant),
           Loop_Content => Loop_Body);

      Loop_Try : constant W_Prog_Id :=
        New_Try_Block
          (Prog    => Sequence (Loop_Start, Loop_Stmt),
           Handler => (1 => New_Handler (Name => Loop_Ident,
                                         Def  => New_Void)));
   begin
      Emit (Body_Params.Theory,
            New_Exception_Declaration (Name => Loop_Ident, Arg  => Why_Empty));

      return
        New_Conditional
          (Condition => +Enter_Condition,
           Then_Part => +Loop_Try);
   end Wrap_Loop;

end Gnat2Why.Expr.Loops;
