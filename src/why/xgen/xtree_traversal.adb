------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                      X T R E E _ T R A V E R S A L                       --
--                                                                          --
--                                B o d y                                  --
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

with Why.Sinfo;      use Why.Sinfo;
with Xtree_Tables;   use Xtree_Tables;
with Xkind_Tables;   use Xkind_Tables;

package body Xtree_Traversal is

   type Kind_Gen_Access is not null access
     procedure (O : in out Output_Record; Kind : Why_Node_Kind);

   Node_Param  : constant String := "Node";
   State_Param : constant String := "State";
   Control     : constant String := State_Param & "." & "Control";
   Depth       : constant String := State_Param & "." & "Depth";

   Node_Renaming : constant String := "This_Node";

   Terminate_Immediately : constant String := "Terminate_Immediately";
   Abandon_Children      : constant String := "Abandon_Children";
   Abandon_Siblings      : constant String := "Abandon_Siblings";
   Continue              : constant String := "Continue";

   Base_State_Type   : constant String := "Traversal_State";
   Stub_State_Type   : constant String := "Traversal_Stub_State";
   Treepr_State_Type : constant String := "Tree_Printer_State";

   procedure Print_Traversal_Op_Declarations
     (O          : in out Output_Record;
      State_Type : String;
      Is_Null    : Boolean := False);
   --  Print the declaration of traversal operations for the given state type;
   --  if Is_Null, then this will be a null procedure declaration.

   procedure Print_Traversal_Op_Specification
     (O          : in out Output_Record;
      Op_Name    : String;
      State_Type : String;
      Kind       : Why_Node_Kind);
   --  Print the subprogram specification of a traversal operation for the
   --  given node kind, state type, and the name of this subprogram
   --  (e.g. "Identifier_Post_Op").

   procedure Print_Kind_Traversal_Implementation
     (O       : in out Output_Record;
      Kind    : Why_Node_Kind;
      In_Stub : Boolean := False);
   --  Print the implementation of a traversal op for the given node kind.
   --  if In_Stub, the body is null and a comment gives the underlying calls
   --  to Traverse.

   procedure Print_Treepr_Pre_Decl
     (O    : in out Output_Record;
      Kind : Why_Node_Kind);
   --  Print the declarative part of a pre-op for tree printing the
   --  given node kind.

   procedure Print_Treepr_Pre_Impl
     (O    : in out Output_Record;
      Kind : Why_Node_Kind);
   --  Print the implementation part (handled sequence of statements)
   --  of a pre-op for tree printing the given node kind.

   procedure Print_Treepr_Post_Impl
     (O    : in out Output_Record;
      Kind : Why_Node_Kind);
   --  Print the implementation part (handled sequence of statements)
   --  of a post-op for tree printing the given node kind.

   procedure Print_Call_To_Traversal_Proc
     (O              : in out Output_Record;
      Traversal_Proc : String;
      FI             : Field_Info;
      Commented_Out  : Boolean := False);
   --  Print a call to the traversal procedure (whose name is given in
   --  parameter) on the child of a node. If Commented_Out, this call
   --  is commented out.

   procedure Print_Traversal_Op_Bodies
     (O          : in out Output_Record;
      State_Type : String;
      Pre_Decl   : Kind_Gen_Access;
      Post_Decl  : Kind_Gen_Access;
      Pre_Impl   : Kind_Gen_Access;
      Post_Impl  : Kind_Gen_Access);
   --  Print the bodies of pre/post ops for the given state type

   procedure Print_Traversal_Op_Stub_Implementation
     (O    : in out Output_Record;
      Kind : Why_Node_Kind);
   --  Print the implementation of a stub of traversal op for the given
   --  kind; underlying calls to Traverse are commented out.

   procedure Start_If_Control
     (O     : in out Output_Record;
      Value : String);
   --  Open an if statement that tests if traversal control equals Value

   procedure End_If (O     : in out Output_Record);
   --  Close an if statement

   procedure Reset_Control (O : in out Output_Record);
   --  Print an statement that sets traversal control back to its initial value

   procedure Reset_If_Control
     (O     : in out Output_Record;
      Value : String);
   --  Print an if statement that resets traversal control if it equals Value

   procedure Reset_Return_If_Control
     (O     : in out Output_Record;
      Value : String);
   --  Print an if statement that:
   --  *  resets traversal control;
   --  * returns;
   --  ... if the traversal control equals Value,

   procedure Return_If_Control
     (O     : in out Output_Record;
      Value : String);
   --  Print an if statement that returns if traversal control equals Value

   procedure Print_Traversal_Params_Unref
     (O    : in out Output_Record;
      Kind : Why_Node_Kind);
   --  Print an declarative part that declares no local variable and
   --  marks traversal op params as unreferenced.

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
      Traversal_Proc : String;
      FI             : Field_Info;
      Commented_Out  : Boolean := False)
   is
      procedure PL_C (O : in out Output_Record; S : String);
      --  Same as PL, but prefix the line with "--  " if Commented_Out
      --  is True.

      --------
      -- PC --
      --------

      procedure PL_C (O : in out Output_Record; S : String) is
      begin
         if Commented_Out then
            P (O, "--  ");
         end if;

         PL (O, S);
      end PL_C;

   --  Start of processing for Print_Call_To_Traversal_Proc

   begin
      PL_C (O, Traversal_Proc);
      PL_C (O, "  (" & State_Param & ",");
      PL_C (O, "   " & Node_Renaming & "." & Field_Name (FI) & ");");
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

      procedure Print_Sub_Traversal (Position : Cursor);
      --  Print the calls to traversal for child at Position

      -------------------------
      -- Print_Sub_Traversal --
      -------------------------

      procedure Print_Sub_Traversal (Position : Cursor) is
         FI : constant Field_Info := Element (Position);
      begin
         if Is_Why_Id (FI) then
            if Is_List (FI) then
               Print_Call_To_Traversal_Proc
                 (O, "Traverse_List", FI, In_Stub);
            else
               Print_Call_To_Traversal_Proc
                 (O, "Traverse", FI, In_Stub);
            end if;
         end if;
      end Print_Sub_Traversal;

   --  Start of processing for Print_Kind_Traversal_Implementation

   begin
      if not In_Stub then
         PL (O, Traversal_Pre_Op (Kind)
             & " (" & State_Param & ", +" & Node_Param & ");");

         NL (O);
         Reset_Return_If_Control (O, Abandon_Children);
         NL (O);
         Return_If_Control (O, Abandon_Siblings);
      end if;

      if Has_Variant_Part (Kind)
        and then (for some E of Why_Tree_Info (Kind).Fields => Is_Why_Id (E))
      then
         NL (O);
         PL (O, "declare");
         Relative_Indent (O, 3);
         PL (O, Node_Renaming & " : Why_Node " &
                "renames Get_Node (" & Node_Param & ");");
         Relative_Indent (O, -3);
         PL (O, "begin");
         Relative_Indent (O, 3);
         Why_Tree_Info (Kind).Fields.Iterate (Print_Sub_Traversal'Access);
         Relative_Indent (O, -3);
         PL (O, "end;");
      end if;

      if not In_Stub then
         NL (O);
         Return_If_Control (O, Terminate_Immediately);
         NL (O);

         PL (O, Traversal_Post_Op (Kind)
             & " (" & State_Param & ", +" & Node_Param & ");");

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
      State_Type : String;
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
      Op_Name    : String;
      State_Type : String;
      Kind       : Why_Node_Kind) is
   begin
      PL (O, "procedure " & Op_Name);
      PL (O, "  (State : in out " & State_Type & ";");
      P  (O, "   Node  : " & Id_Subtype (Kind, Derived) & ")");
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
      State_Type : String;
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

   procedure Print_Traverse_Body (O : in out Output_Record) is
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
      null;
   end Print_Treepr_Pre_Decl;

   ---------------------------
   -- Print_Treepr_Pre_Impl --
   ---------------------------

   procedure Print_Treepr_Pre_Impl
     (O       : in out Output_Record;
      Kind    : Why_Node_Kind)
   is
      use Node_Lists;

      procedure Print_Sub_Traversal (Position : Cursor);
      --  Print calls to traversals for child at Position

      -------------------------
      -- Print_Sub_Traversal --
      -------------------------

      procedure Print_Sub_Traversal (Position : Cursor) is
         FI    : constant Field_Info := Element (Position);
         Field : constant String :=
                   "Get_Node (+" & Node_Param & ")." & Field_Name (FI);
      begin
         if Is_Why_Id (FI) and then Maybe_Null (FI) then
            if Is_List (FI) then
               PL (O, "if not Is_Empty (" & Field & ") then");
            else
               PL (O, "if " & Field & " /= Why_Empty then");
            end if;

            Relative_Indent (O, 3);
         end if;

         PL (O, "P (O, """ & Param_Name (FI) & ": "");");
         PL (O, "Relative_Indent (O, 1);");

         if Is_Why_Id (FI) then
            declare
               Traversal_Proc : constant String :=
                                  (if Is_List (FI) then "Traverse_List"
                                   else "Traverse");
            begin
               PL (O, Traversal_Proc);
               PL (O, "  (" & State_Param & ",");
               PL (O, "   " & Field & ");");
            end;

         else
            PL (O, "P (O, " & Field & ");");
            PL (O, "NL (O);");
         end if;

         PL (O, "Relative_Indent (O, -1);");

         if Is_Why_Id (FI) and then Maybe_Null (FI) then
            Relative_Indent (O, -3);
            PL (O, "end if;");
         end if;
      end Print_Sub_Traversal;

   --  Start of processing for Print_Treepr_Pre_Impl

   begin
      PL (O, "P (O, """ & Mixed_Case_Name (Kind) & """);");
      PL (O, "P (O, "" (Node_Id="");");
      PL (O, "P (O, +" & Node_Param & ");");
      PL (O, "P (O, "")"");");
      PL (O, "NL (O);");
      PL (O, "if State.Depth /= 0 then");
      Relative_Indent (O, 3);
      PL (O, Depth & " := " & Depth & " - 1;");
      PL (O, "Relative_Indent (O, 1);");

      for FI of Common_Fields.Fields loop
         if Field_Kind (FI) /= Field_Special then
            PL (O, "P (O, """ & Param_Name (FI) & ": "");");
            PL (O, "P (O, "
                & Accessor_Name (W_Unused_At_Start, Regular, FI)
                & " (+" & Node_Param & "));");
            PL (O, "NL (O);");
         end if;
      end loop;

      if Has_Variant_Part (Kind) then
         Why_Tree_Info (Kind).Fields.Iterate (Print_Sub_Traversal'Access);
      end if;

      PL (O, "Relative_Indent (O, -1);");
      PL (O, Depth & " := " & Depth & " + 1;");
      Relative_Indent (O, -3);
      PL (O, "end if;");
      PL (O, Control & " := Abandon_Children;");
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
      PL (O, "null;");
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
      Value : String)
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
      Value : String)
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
      Value : String)
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
      Value : String)
   is
   begin
      PL (O, "if " & Control & " = " & Value & " then");
      Relative_Indent (O, 3);
   end Start_If_Control;

end Xtree_Traversal;
