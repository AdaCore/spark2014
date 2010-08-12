------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                      X T R E E _ T R A V E R S A L                       --
--                                                                          --
--                                B o d y                                  --
--                                                                          --
--                       Copyright (C) 2010, AdaCore                        --
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

with Ada.Containers; use Ada.Containers;
with Why.Sinfo;      use Why.Sinfo;
with Xtree_Tables;   use Xtree_Tables;

package body Xtree_Traversal is

   Node_Param  : constant Wide_String := "Node";
   State_Param : constant Wide_String := "State";
   Control     : constant Wide_String := State_Param & "." & "Control";

   Terminate_Immediately : constant Wide_String := "Terminate_Immediately";
   Abandon_Children      : constant Wide_String := "Abandon_Children";
   Abandon_Siblings      : constant Wide_String := "Abandon_Siblings";
   Continue              : constant Wide_String := "Continue";

   procedure Print_Traversal_Op_Specification
     (O       : in out Output_Record;
      Op_Name : Wide_String;
      Kind    : Why_Node_Kind);

   procedure Print_Kind_Traversal_Implementation
     (O    : in out Output_Record;
      Kind : Why_Node_Kind);

   procedure Print_Call_To_Traversal_Proc
     (O              : in out Output_Record;
      Traversal_Proc : Wide_String;
      Kind           : Why_Node_Kind;
      FI             : Field_Info);

   procedure Start_If_Control
     (O     : in out Output_Record;
      Value : Wide_String);

   procedure End_If (O     : in out Output_Record);

   procedure Reset_Control (O : in out Output_Record);

   procedure Reset_If_Control
     (O     : in out Output_Record;
      Value : Wide_String);

   procedure Reset_Return_If_Control
     (O     : in out Output_Record;
      Value : Wide_String);

   procedure Return_If_Control
     (O     : in out Output_Record;
      Value : Wide_String);

   ------------
   -- End_If --
   ------------

   procedure End_If (O     : in out Output_Record) is
   begin
      Relative_Indent (O, -3);
      PL (O, "end if;");
   end End_If;

   ----------------------------------
   -- Print_Call_To_Traversal_Proc --
   ----------------------------------

   procedure Print_Call_To_Traversal_Proc
     (O              : in out Output_Record;
      Traversal_Proc : Wide_String;
      Kind           : Why_Node_Kind;
      FI             : Field_Info) is
   begin
      PL (O, Traversal_Proc);
      PL (O, "  (" & State_Param & ",");
      PL (O, "   " & Accessor_Name (Kind, FI) & " (" & Node_Param & "));");
   end Print_Call_To_Traversal_Proc;

   -----------------------------------------
   -- Print_Kind_Traversal_Implementation --
   -----------------------------------------

   procedure Print_Kind_Traversal_Implementation
     (O    : in out Output_Record;
      Kind : Why_Node_Kind)
   is
      use Node_Lists;

      First_Child : Boolean := True;

      procedure Print_Sub_Traversal (Position : Cursor);

      -------------------------
      -- Print_Sub_Traversal --
      -------------------------

      procedure Print_Sub_Traversal (Position : Cursor) is
         FI : constant Field_Info := Element (Position);
      begin
         if Is_Why_Id (FI) then
            if First_Child then
               NL (O);
               First_Child := False;
            end if;

            if Is_List (FI) then
               Print_Call_To_Traversal_Proc (O, "Traverse_List", Kind, FI);
            else
               Print_Call_To_Traversal_Proc (O, "Traverse", Kind, FI);
            end if;
         end if;
      end Print_Sub_Traversal;

   begin
      PL (O, Traversal_Pre_Op (Kind)
          & " (" & State_Param & ", " & Node_Param & ");");

      NL (O);
      Reset_Return_If_Control (O, Abandon_Children);
      NL (O);
      Return_If_Control (O, Abandon_Siblings);

      if Has_Variant_Part (Kind) then
         Why_Tree_Info (Kind).Fields.Iterate (Print_Sub_Traversal'Access);
      end if;

      NL (O);
      Return_If_Control (O, Terminate_Immediately);
      NL (O);

      PL (O, Traversal_Post_Op (Kind)
          & " (" & State_Param & ", " & Node_Param & ");");

      NL (O);
      Reset_If_Control (O, Abandon_Siblings);
      NL (O);
      Return_If_Control (O, Terminate_Immediately);
   end Print_Kind_Traversal_Implementation;

   -------------------------------------
   -- Print_Traversal_Op_Declarations --
   -------------------------------------

   procedure Print_Traversal_Op_Declarations  (O : in out Output_Record) is
   begin
      for J in Valid_Kind'Range loop
         Print_Traversal_Op_Specification (O, Traversal_Pre_Op (J), J);
         PL (O, "  is null;");
         NL (O);

         Print_Traversal_Op_Specification (O, Traversal_Post_Op (J), J);
         PL (O, "  is null;");

         if J /= Valid_Kind'Last then
            NL (O);
         end if;
      end loop;
   end Print_Traversal_Op_Declarations;

   --------------------------------------
   -- Print_Traversal_Op_Specification --
   --------------------------------------

   procedure Print_Traversal_Op_Specification
     (O       : in out Output_Record;
      Op_Name : Wide_String;
      Kind    : Why_Node_Kind) is
   begin
      PL (O, "procedure " & Op_Name);
      PL (O, "  (State : in out Traversal_State;");
      PL (O, "   Node  : " & Id_Type_Name (Kind) & ")");
   end Print_Traversal_Op_Specification;

   -------------------------
   -- Print_Traverse_Body --
   -------------------------

   procedure Print_Traverse_Body  (O : in out Output_Record) is
   begin
      Return_If_Control (O, Terminate_Immediately);
      NL (O);
      Return_If_Control (O, Abandon_Siblings);
      NL (O);

      PL (O, "if " & Node_Param & " = Why_Empty then");
      PL (O, "   return;");
      PL (O, "end if;");
      NL (O);

      PL (O, "case Get_Kind (" & Node_Param & ") is");
      Relative_Indent (O, 3);
      for J in Valid_Kind'Range loop
         PL (O, "when " & Mixed_Case_Name (J) & " =>");
         Relative_Indent (O, 3);
         Print_Kind_Traversal_Implementation (O, J);
         Relative_Indent (O, -3);
         NL (O);
      end loop;
      PL (O, "when others =>");
      PL (O, "   pragma Assert (False);");
      Relative_Indent (O, -3);
      P (O, "end case;");
   end Print_Traverse_Body;

   -------------------
   -- Reset_Control --
   -------------------

   procedure Reset_Control (O : in out Output_Record) is
   begin
      PL (O, Control & " := " & Continue & ";");
   end Reset_Control;

   ----------------------
   -- Reset_If_Control --
   ----------------------

   procedure Reset_If_Control
     (O     : in out Output_Record;
      Value : Wide_String)
   is
   begin
      Start_If_Control (O, Value);
      Reset_Control (O);
      End_If (O);
   end Reset_If_Control;

   -----------------------------
   -- Reset_Return_If_Control --
   -----------------------------

   procedure Reset_Return_If_Control
     (O     : in out Output_Record;
      Value : Wide_String)
   is
   begin
      Start_If_Control (O, Value);
      Reset_Control (O);
      PL (O, "return;");
      End_If (O);
   end Reset_Return_If_Control;

   -----------------------
   -- Return_If_Control --
   -----------------------

   procedure Return_If_Control
     (O     : in out Output_Record;
      Value : Wide_String)
   is
   begin
      Start_If_Control (O, Value);
      PL (O, "return;");
      End_If (O);
   end Return_If_Control;

   --------------------
   -- Start_If_Control --
   --------------------

   procedure Start_If_Control
     (O     : in out Output_Record;
      Value : Wide_String)
   is
   begin
      PL (O, "if " & Control & " = " & Value & " then");
      Relative_Indent (O, 3);
   end Start_If_Control;

end Xtree_Traversal;
