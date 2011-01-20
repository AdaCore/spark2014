------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                      X T R E E _ T R A V E R S A L                       --
--                                                                          --
--                                B o d y                                  --
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

with Why.Sinfo;      use Why.Sinfo;
with Xtree_Tables;   use Xtree_Tables;

package body Xtree_Traversal is

   type Kind_Gen_Access is not null access
     procedure (O : in out Output_Record; Kind : Why_Node_Kind);

   Node_Param  : constant Wide_String := "Node";
   State_Param : constant Wide_String := "State";
   Control     : constant Wide_String := State_Param & "." & "Control";

   Terminate_Immediately : constant Wide_String := "Terminate_Immediately";
   Abandon_Children      : constant Wide_String := "Abandon_Children";
   Abandon_Siblings      : constant Wide_String := "Abandon_Siblings";
   Continue              : constant Wide_String := "Continue";

   Base_State_Type   : constant Wide_String := "Traversal_State";
   Stub_State_Type   : constant Wide_String := "Traversal_Stub_State";
   Treepr_State_Type : constant Wide_String := "Tree_Printer_State";

   procedure Print_Traversal_Op_Declarations
     (O          : in out Output_Record;
      State_Type : Wide_String;
      Is_Null    : Boolean := False);
   --  ??? Missing doc

   procedure Print_Traversal_Op_Specification
     (O          : in out Output_Record;
      Op_Name    : Wide_String;
      State_Type : Wide_String;
      Kind       : Why_Node_Kind);
   --  ??? Missing doc

   procedure Print_Kind_Traversal_Implementation
     (O       : in out Output_Record;
      Kind    : Why_Node_Kind;
      In_Stub : Boolean := False);
   --  ??? Missing doc

   procedure Print_Treepr_Pre_Decl
     (O    : in out Output_Record;
      Kind : Why_Node_Kind);
   --  ??? Missing doc

   procedure Print_Treepr_Pre_Impl
     (O    : in out Output_Record;
      Kind : Why_Node_Kind);
   --  ??? Missing doc

   procedure Print_Treepr_Post_Impl
     (O    : in out Output_Record;
      Kind : Why_Node_Kind);
   --  ??? Missing doc

   procedure Print_Call_To_Traversal_Proc
     (O              : in out Output_Record;
      Traversal_Proc : Wide_String;
      Kind           : Why_Node_Kind;
      FI             : Field_Info;
      Commented_Out  : Boolean := False);
   --  ??? Missing doc

   procedure Print_Traversal_Op_Bodies
     (O          : in out Output_Record;
      State_Type : Wide_String;
      Pre_Decl   : Kind_Gen_Access;
      Post_Decl  : Kind_Gen_Access;
      Pre_Impl   : Kind_Gen_Access;
      Post_Impl  : Kind_Gen_Access);
   --  ??? Missing doc

   procedure Print_Traversal_Op_Stub_Implementation
     (O    : in out Output_Record;
      Kind : Why_Node_Kind);
   --  ??? Missing doc

   procedure Start_If_Control
     (O     : in out Output_Record;
      Value : Wide_String);
   --  ??? Missing doc

   procedure End_If (O     : in out Output_Record);
   --  ??? Missing doc

   procedure Reset_Control (O : in out Output_Record);
   --  ??? Missing doc

   procedure Reset_If_Control
     (O     : in out Output_Record;
      Value : Wide_String);
   --  ??? Missing doc

   procedure Reset_Return_If_Control
     (O     : in out Output_Record;
      Value : Wide_String);
   --  ??? Missing doc

   procedure Return_If_Control
     (O     : in out Output_Record;
      Value : Wide_String);
   --  ??? Missing doc

   procedure Print_Traversal_Params_Unref
     (O    : in out Output_Record;
      Kind : Why_Node_Kind);
   --  ??? Missing doc

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
      FI             : Field_Info;
      Commented_Out  : Boolean := False)
   is
      procedure PL_C (O : in out Output_Record; S : Wide_String);

      --------
      -- PC --
      --------

      procedure PL_C (O : in out Output_Record; S : Wide_String) is
      begin
         if Commented_Out then
            P (O, "--  ");
         end if;

         PL (O, S);
      end PL_C;

   begin
      PL_C (O, Traversal_Proc);
      PL_C (O, "  (" & State_Param & ",");
      PL_C (O, "   " & Accessor_Name (Kind, FI) & " (" & Node_Param & "));");
   end Print_Call_To_Traversal_Proc;

   -----------------------------------------
   -- Print_Kind_Traversal_Implementation --
   -----------------------------------------

   procedure Print_Kind_Traversal_Implementation
     (O       : in out Output_Record;
      Kind    : Why_Node_Kind;
      In_Stub : Boolean := False)
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
               Print_Call_To_Traversal_Proc
                 (O, "Traverse_List", Kind, FI, In_Stub);
            else
               Print_Call_To_Traversal_Proc
                 (O, "Traverse", Kind, FI, In_Stub);
            end if;
         end if;
      end Print_Sub_Traversal;

   begin
      if not In_Stub then
         PL (O, Traversal_Pre_Op (Kind)
             & " (" & State_Param & ", " & Node_Param & ");");

         NL (O);
         Reset_Return_If_Control (O, Abandon_Children);
         NL (O);
         Return_If_Control (O, Abandon_Siblings);
      end if;

      if Has_Variant_Part (Kind) then
         Why_Tree_Info (Kind).Fields.Iterate (Print_Sub_Traversal'Access);
      end if;

      if not In_Stub then
         NL (O);
         Return_If_Control (O, Terminate_Immediately);
         NL (O);

         PL (O, Traversal_Post_Op (Kind)
             & " (" & State_Param & ", " & Node_Param & ");");

         NL (O);
         Reset_If_Control (O, Abandon_Siblings);
         NL (O);
         Return_If_Control (O, Terminate_Immediately);
      end if;
   end Print_Kind_Traversal_Implementation;

   -------------------------------------
   -- Print_Traversal_Op_Declarations --
   -------------------------------------

   procedure Print_Traversal_Op_Declarations (O : in out Output_Record) is
   begin
      Print_Traversal_Op_Declarations (O, Base_State_Type, True);
   end Print_Traversal_Op_Declarations;

   procedure Print_Traversal_Op_Declarations
     (O          : in out Output_Record;
      State_Type : Wide_String;
      Is_Null    : Boolean := False)
   is
   begin
      for J in Valid_Kind'Range loop
         Print_Traversal_Op_Specification
           (O, Traversal_Pre_Op (J), State_Type, J);

         if Is_Null then
            NL (O);
            PL (O, "  is null;");
         else
            PL (O, ";");
         end if;

         NL (O);
         Print_Traversal_Op_Specification
           (O, Traversal_Post_Op (J), State_Type, J);

         if Is_Null then
            NL (O);
            PL (O, "  is null;");
         else
            PL (O, ";");
         end if;

         if J /= Valid_Kind'Last then
            NL (O);
         end if;
      end loop;
   end Print_Traversal_Op_Declarations;

   --------------------------------------
   -- Print_Traversal_Op_Specification --
   --------------------------------------

   procedure Print_Traversal_Op_Specification
     (O          : in out Output_Record;
      Op_Name    : Wide_String;
      State_Type : Wide_String;
      Kind       : Why_Node_Kind) is
   begin
      PL (O, "procedure " & Op_Name);
      PL (O, "  (State : in out " & State_Type & ";");
      P  (O, "   Node  : " & Id_Type_Name (Kind) & ")");
   end Print_Traversal_Op_Specification;

   ------------------------------------------
   -- Print_Traversal_Op_Stub_Declarations --
   ------------------------------------------

   procedure Print_Traversal_Op_Stub_Declarations
     (O : in out Output_Record) is
   begin
      Print_Traversal_Op_Declarations (O, Stub_State_Type);
   end Print_Traversal_Op_Stub_Declarations;

   ------------------------------------
   -- Print_Traversal_Op_Stub_Bodies --
   ------------------------------------

   procedure Print_Traversal_Op_Stub_Bodies (O : in out Output_Record) is
   begin
      Print_Traversal_Op_Bodies
        (O,
         Stub_State_Type,
         Print_Traversal_Params_Unref'Access,
         Print_Traversal_Params_Unref'Access,
         Print_Traversal_Op_Stub_Implementation'Access,
         Print_Traversal_Op_Stub_Implementation'Access);
   end Print_Traversal_Op_Stub_Bodies;

   -------------------------------
   -- Print_Traversal_Op_Bodies --
   -------------------------------

   procedure Print_Traversal_Op_Bodies
     (O          : in out Output_Record;
      State_Type : Wide_String;
      Pre_Decl   : Kind_Gen_Access;
      Post_Decl  : Kind_Gen_Access;
      Pre_Impl   : Kind_Gen_Access;
      Post_Impl  : Kind_Gen_Access)
   is
   begin
      for J in Valid_Kind'Range loop
         Print_Box (O, Traversal_Pre_Op (J));
         NL (O);

         Print_Traversal_Op_Specification
           (O, Traversal_Pre_Op (J), State_Type, J);
         NL (O);
         PL (O, "is");
         Relative_Indent (O, 3);
         Pre_Decl (O, J);
         Relative_Indent (O, -3);
         PL (O, "begin");
         Relative_Indent (O, 3);
         Pre_Impl (O, J);
         Relative_Indent (O, -3);
         PL (O, "end " & Traversal_Pre_Op (J) & ";");
         NL (O);

         Print_Box (O, Traversal_Post_Op (J));
         NL (O);

         Print_Traversal_Op_Specification
           (O, Traversal_Post_Op (J), State_Type, J);
         NL (O);
         PL (O, "is");
         Relative_Indent (O, 3);
         Post_Decl (O, J);
         Relative_Indent (O, -3);
         PL (O, "begin");
         Relative_Indent (O, 3);
         Post_Impl (O, J);
         Relative_Indent (O, -3);
         PL (O, "end " & Traversal_Post_Op (J) & ";");

         if J /= Valid_Kind'Last then
            NL (O);
         end if;
      end loop;
   end Print_Traversal_Op_Bodies;

   --------------------------------------------
   -- Print_Traversal_Op_Stub_Implementation --
   --------------------------------------------

   procedure Print_Traversal_Op_Stub_Implementation
     (O    : in out Output_Record;
      Kind : Why_Node_Kind) is
   begin
      PL (O, "raise Not_Implemented;");
      Print_Kind_Traversal_Implementation (O, Kind, True);
   end Print_Traversal_Op_Stub_Implementation;

   ----------------------------------
   -- Print_Traversal_Params_Unref --
   ----------------------------------

   procedure Print_Traversal_Params_Unref
     (O    : in out Output_Record;
      Kind : Why_Node_Kind) is
      pragma Unreferenced (Kind);
   begin
      PL (O, "pragma Unreferenced (Node);");
      PL (O, "pragma Unreferenced (State);");
   end Print_Traversal_Params_Unref;

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
      PL (O, "end case;");
   end Print_Traverse_Body;

   ---------------------------
   -- Print_Treepr_Pre_Decl --
   ---------------------------

   procedure Print_Treepr_Pre_Decl
     (O    : in out Output_Record;
      Kind : Why_Node_Kind)
   is
   begin
      PL (O, "pragma Unreferenced (State);");

      if Kind /= W_Identifier then
         PL (O, "pragma Unreferenced (Node);");
      end if;
   end Print_Treepr_Pre_Decl;

   ---------------------------
   -- Print_Treepr_Pre_Impl --
   ---------------------------

   procedure Print_Treepr_Pre_Impl
     (O    : in out Output_Record;
      Kind : Why_Node_Kind)
   is
   begin
      PL (O, "P (O, """ & Why_Node_Kind'Wide_Image (Kind) & """);");

      if Kind = W_Identifier then
         PL (O, "P (O, "" : "");");
         PL (O, "P (O, Get_Name_String (Get_Node (Node).Symbol));");
      end if;

      PL (O, "NL (O);");
      PL (O, "Relative_Indent (O, 1);");
   end Print_Treepr_Pre_Impl;

   ----------------------------
   -- Print_Treepr_Post_Impl --
   ----------------------------

   procedure Print_Treepr_Post_Impl
     (O    : in out Output_Record;
      Kind : Why_Node_Kind)
   is
      pragma Unreferenced (Kind);
   begin
      PL (O, "Relative_Indent (O, -1);");
   end Print_Treepr_Post_Impl;

   --------------------------------------
   -- Print_Treepr_Traversal_Op_Bodies --
   --------------------------------------

   procedure Print_Treepr_Traversal_Op_Bodies (O : in out Output_Record) is
   begin
      Print_Traversal_Op_Bodies
        (O,
         Treepr_State_Type,
         Print_Treepr_Pre_Decl'Access,
         Print_Traversal_Params_Unref'Access,
         Print_Treepr_Pre_Impl'Access,
         Print_Treepr_Post_Impl'Access);
   end Print_Treepr_Traversal_Op_Bodies;

   --------------------------------------------
   -- Print_Treepr_Traversal_Op_Declarations --
   --------------------------------------------

   procedure Print_Treepr_Traversal_Op_Declarations
     (O : in out Output_Record) is
   begin
      Print_Traversal_Op_Declarations (O, Treepr_State_Type);
   end Print_Treepr_Traversal_Op_Declarations;

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
