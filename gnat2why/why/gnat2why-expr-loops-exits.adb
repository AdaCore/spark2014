------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--             G N A T 2 W H Y - E X P R - L O O P S - E X I T S            --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                     Copyright (C) 2018-2019, AdaCore                     --
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
      function Is_Loop_Stmt (N : Node_Id) return Boolean is
        (Nkind (N) = N_Loop_Statement);

      function Enclosing_Loop_Stmt is new
        First_Parent_With_Property (Is_Loop_Stmt);

      Loop_Stmt : constant Node_Id :=
        Enclosing_Loop_Stmt (Nlists.First (Instrs));

   begin
      if Present (Loop_Stmt)
        and then not Is_Selected_For_Loop_Unrolling (Loop_Stmt)
        and then List_Length (Instrs) > 1
        and then Unconditional_Loop_Exit (Nlists.Last (Instrs))
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
