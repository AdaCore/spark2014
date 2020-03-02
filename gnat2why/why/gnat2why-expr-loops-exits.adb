------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--             G N A T 2 W H Y - E X P R - L O O P S - E X I T S            --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                     Copyright (C) 2018-2020, AdaCore                     --
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

with GNATCOLL.Symbols;   use GNATCOLL.Symbols;
with String_Utils;       use String_Utils;
with Why.Atree.Builders; use Why.Atree.Builders;
with Why.Conversions;    use Why.Conversions;
with Why.Gen.Decl;       use Why.Gen.Decl;
with Why.Gen.Names;      use Why.Gen.Names;

package body Gnat2Why.Expr.Loops.Exits is

   Subprogram_Exit_Exceptions : Why_Node_Sets.Set;
   --  Set of exception declarations

   Loop_Exit_Statements : Why_Node_Maps_Lists.List;
   --  List of mapping from exception name to corresponding program, for these
   --  parts of a loop that unconditionally exit or return. A new context is
   --  pushed at every loop start by calling [Before_Start_Of_Loop], and popped
   --  after loop end by calling [Wrap_Loop_Body].

   -----------------------------
   -- Unconditional_Loop_Exit --
   -----------------------------

   --  Local helper function defined first for use in other subprograms

   function Unconditional_Loop_Exit (N : Node_Id) return Boolean is
     ((Nkind (N) = N_Exit_Statement and then No (Condition (N)))
         or else
       Nkind (N) in N_Simple_Return_Statement
                  | N_Extended_Return_Statement);

   --------------------------
   -- Before_Start_Of_Loop --
   --------------------------

   procedure Before_Start_Of_Loop is
   begin
      Loop_Exit_Statements.Prepend (Why_Node_Maps.Empty_Map);
   end Before_Start_Of_Loop;

   --------------------------------
   -- Before_Start_Of_Subprogram --
   --------------------------------

   procedure Before_Start_Of_Subprogram is
   begin
      Subprogram_Exit_Exceptions.Clear;
   end Before_Start_Of_Subprogram;

   ------------------------
   -- Declare_Exceptions --
   ------------------------

   procedure Declare_Exceptions (File : W_Section_Id) is
   begin
      for Exc of Subprogram_Exit_Exceptions loop
         Emit (File, New_Exception_Declaration (Name => +Exc));
      end loop;
   end Declare_Exceptions;

   ------------------------
   -- Record_And_Replace --
   ------------------------

   --  If inside a loop, with the last instruction being an unconditional exit
   --  or return statement, and provided the loop is not unrolled, we store the
   --  Why3 expression in a map, and return instead the raise expression that
   --  will be linked to that treatment.

   procedure Record_And_Replace
     (Instrs : List_Id;
      Expr   : in out W_Prog_Id)
   is
      function Ends_In_Unconditional_Exit (Stmts : List_Id) return Boolean is
        (Unconditional_Loop_Exit (Nlists.Last (Stmts)));

      --  Identify the direct enclosing loop statement. It might not be the
      --  same as the loop that the exit statement exits from.

      function Is_Loop_Stmt (N : Node_Id) return Boolean is
        (Nkind (N) = N_Loop_Statement);

      function Enclosing_Loop_Stmt is new
        First_Parent_With_Property (Is_Loop_Stmt);

      Loop_Stmt : constant Node_Id :=
        Enclosing_Loop_Stmt (Nlists.First (Instrs));

      --  Identify a parent node inside the loop which is part of a list ending
      --  in an unconditional exit, if any, so that we don't perform the
      --  optimization in that case.

      function Leads_To_Exit (N : Node_Id) return Boolean is
        (Is_List_Member (N)
         and then Ends_In_Unconditional_Exit (List_Containing (N)));

      function Is_Loop_Or_Leads_To_Exit (N : Node_Id) return Boolean is
        (Is_Loop_Stmt (N) or else Leads_To_Exit (N));

      function Enclosing_Loop_Or_Not_Stmt is new
        First_Parent_With_Property (Is_Loop_Or_Leads_To_Exit);

      Loop_Or_Not_Stmt : constant Node_Id :=
        Enclosing_Loop_Or_Not_Stmt (Nlists.First (Instrs));

   --  Start of processing for Record_And_Replace

   begin
      if Present (Loop_Stmt)

        --  If there is a parent node inside the loop that is part of a list
        --  ending in an unconditional exit, then the current code will be
        --  hoisted out of the loop as part of this parent node. Do not hoist
        --  it here, as this would lead to the new exception raised not being
        --  caught.

        and then Loop_Stmt = Loop_Or_Not_Stmt

        --  Do not perform this optimization for loops that are already
        --  unrolled.

        and then not Is_Selected_For_Loop_Unrolling (Loop_Stmt)

        --  No benefit in doing this unless there are instructions before
        --  the exit statement.

        and then List_Length (Instrs) > 1

        --  Currently only do this optimization for list of statements that
        --  end up in an unconditional exit. Possibly do this also for return
        --  statements in the future???

        and then Ends_In_Unconditional_Exit (Instrs)
      then
         declare
            Name : constant Symbol :=
              NID (Capitalize_First
                     (New_Temp_Identifier (Base_Name => "exception")));
            Exc : constant W_Name_Id := New_Name (Symb => Name);

            procedure Add_In_Map (M : in out Why_Node_Maps.Map);
            --  Add the new mapping to the toplevel map in the loop contexts

            procedure Add_In_Map (M : in out Why_Node_Maps.Map) is
            begin
               M.Insert (+Exc, +Expr);
            end Add_In_Map;

         begin
            Subprogram_Exit_Exceptions.Insert (+Exc);

            --  All blocks of code that end up in an exit statement are
            --  associated to the closest enclosing loop. We could improve on
            --  that optimization for exit statements that exit more than the
            --  direct enclosing loop:
            --
            --     Loop_1: while Cond1 loop
            --       Loop_2: while Cond2 loop
            --         ...
            --              <some-code>
            --              exit Cond1;
            --         ...
            --
            --  In the case above, <some-code> will be hoisted out of the Why3
            --  loop for Loop_2, but still inside the Why3 loop for Loop_1.
            --  We cannot simply associate this code to Loop_1, as <some-code>
            --  might itself contain an exit statement for Loop_1.

            Loop_Exit_Statements.Update_Element
              (Position => Loop_Exit_Statements.First,
               Process  => Add_In_Map'Access);
            Expr := New_Raise (Name => Exc);
         end;
      end if;
   end Record_And_Replace;

   --------------------
   -- Wrap_Loop_Body --
   --------------------

   procedure Wrap_Loop_Body (Loop_Body : in out W_Prog_Id) is
      M : constant Why_Node_Maps.Map := Loop_Exit_Statements.First_Element;

   begin
      Loop_Exit_Statements.Delete_First;

      if not M.Is_Empty then
         declare
            Exit_Handlers : W_Handler_Array (1 .. Integer (M.Length));
            Exit_Handler  : Why_Node_Maps.Cursor := M.First;

            use Why_Node_Maps;
         begin
            for J in Exit_Handlers'Range loop
               Exit_Handlers (J) :=
                 New_Handler (Name => +Key (Exit_Handler),
                              Def  => +Element (Exit_Handler));
               Next (Exit_Handler);
            end loop;

            Loop_Body := New_Try_Block (Prog    => Loop_Body,
                                        Handler => Exit_Handlers);
         end;
      end if;
   end Wrap_Loop_Body;

end Gnat2Why.Expr.Loops.Exits;
