------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                       X T R E E _ B U I L D E R S                        --
--                                                                          --
--                                 S p e c                                  --
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

with Why.Sinfo;     use Why.Sinfo;
with Xtree_Tables;  use Xtree_Tables;
with Xkind_Tables;  use Xkind_Tables;
with Xtree_Classes; use Xtree_Classes;

package body Xtree_Builders is

   Node_Id_Param : constant Wide_String := "Id";
   New_Node      : constant Wide_String := "Result";

   procedure Print_Builder_Declaration
     (O    : in out Output_Record;
      Kind : Why_Node_Kind;
      BK   : Builder_Kind);
   --  Print builder declaration for the given node kind

   procedure Print_Builder_Specification
     (O    : in out Output_Record;
      Kind : Why_Node_Kind;
      BK   : Builder_Kind);
   --  Print builder specification for the given node kind

   procedure Print_Builder_Postcondition
     (O    : in out Output_Record;
      Kind : Why_Node_Kind;
      BK   : Builder_Kind);
   --  Print builder postcondition for the given node kind

   procedure Print_Builder_Precondition
     (O    : in out Output_Record;
      Kind : Why_Node_Kind;
      BK   : Builder_Kind);
   --  Print builder precondition for the given node kind.
   --  Note that this precondition can be replaced nicely
   --  replaced by a subtype predicate on ids; when subtype
   --  predicates are supported by GNAT, it will be a good time
   --  to do the substitution.

   procedure Print_Builder_Body
     (O    : in out Output_Record;
      Kind : Why_Node_Kind;
      BK   : Builder_Kind);
   --  Print builder body for the given node kind

   procedure Print_Builder_Implementation
     (O    : in out Output_Record;
      Kind : Why_Node_Kind;
      BK   : Builder_Kind);
   --  Print the handled sequence of statements that implements this builder

   procedure Print_Builder_Local_Declarations
     (O    : in out Output_Record;
      Kind : Why_Node_Kind;
      BK   : Builder_Kind);
   --  Print the local declarations in builder body

   procedure Print_Class_Copy_Builder_Body
     (O  : in out Output_Record;
      CI : Class_Info);

   procedure Print_Class_Copy_Builder_Declaration
     (O      : in out Output_Record;
      Prefix : Wide_String);

   procedure Print_Class_Copy_Builder_Specification
     (O      : in out Output_Record;
      Prefix : Wide_String);

   procedure Adjust_Columns
     (O        : in out Output_Record;
      Name_Len : Positive;
      Max_Len  : Positive);

   --------------------
   -- Adjust_Columns --
   --------------------

   procedure Adjust_Columns
     (O        : in out Output_Record;
      Name_Len : Positive;
      Max_Len  : Positive) is
   begin
      for J in Name_Len .. Max_Len loop
         P (O, " ");
      end loop;
   end Adjust_Columns;

   --------------------------
   -- Print_Builder_Bodies --
   --------------------------

   procedure Print_Builder_Bodies (O : in out Output_Record) is
   begin
      for J in Valid_Kind'Range loop
         Print_Builder_Body (O, J, Builder_Regular);

         if J /= Why_Tree_Info'Last then
            NL (O);
         end if;
      end loop;
   end Print_Builder_Bodies;

   ------------------------
   -- Print_Builder_Body --
   ------------------------

   procedure Print_Builder_Body
     (O    : in out Output_Record;
      Kind : Why_Node_Kind;
      BK   : Builder_Kind)
   is
      BN : constant Wide_String := Builder_Name (Kind, BK);
   begin
      Print_Box (O, BN);
      NL (O);

      Print_Builder_Specification (O, Kind, BK);
      NL (O);
      PL (O, "is");

      if BK = Builder_Copy then
         PL (O, "begin");
         Relative_Indent (O, 3);
         PL (O, "if " & Node_Id_Param & " = Why_Empty then");
         PL (O, "   return Why_Empty;");
         PL (O, "end if;");
         NL (O);
         PL (O, "declare");
      end if;

      Relative_Indent (O, 3);
      Print_Builder_Local_Declarations (O, Kind, BK);
      Relative_Indent (O, -3);
      PL (O, "begin");
      Relative_Indent (O, 3);
      Print_Builder_Implementation (O, Kind, BK);
      Relative_Indent (O, -3);

      if BK = Builder_Copy then
         PL (O, "end;");
         Relative_Indent (O, -3);
      end if;

      PL (O, "end " & BN & ";");
   end Print_Builder_Body;

   --------------------------------
   -- Print_Builder_Declarations --
   --------------------------------

   procedure Print_Builder_Declarations
     (O  : in out Output_Record)
   is
   begin
      for J in Valid_Kind'Range loop
         Print_Builder_Declaration (O, J, Builder_Regular);

         if J /= Why_Tree_Info'Last then
            NL (O);
         end if;
      end loop;
   end Print_Builder_Declarations;

   -------------------------------
   -- Print_Builder_Declaration --
   -------------------------------

   procedure Print_Builder_Declaration
     (O    : in out Output_Record;
      Kind : Why_Node_Kind;
      BK   : Builder_Kind) is
   begin
      Print_Builder_Specification (O, Kind, BK);
      PL (O, ";");
      Print_Builder_Precondition (O, Kind, BK);
      Print_Builder_Postcondition (O, Kind, BK);
   end Print_Builder_Declaration;

   ----------------------------------
   -- Print_Builder_Implementation --
   ----------------------------------

   procedure Print_Builder_Implementation
     (O    : in out Output_Record;
      Kind : Why_Node_Kind;
      BK   : Builder_Kind)
   is
      use Node_Lists;

      Variant_Part : constant Why_Node_Info := Why_Tree_Info (Kind);

      procedure Print_Record_Initialization (Position : Cursor);

      ---------------------------------
      -- Print_Record_Initialization --
      ---------------------------------

      procedure Print_Record_Initialization (Position : Cursor) is
         FI : constant Field_Info := Element (Position);
         FN : constant Wide_String := Field_Name (FI);
      begin
         if BK = Builder_Unchecked then
            P (O, New_Node & "." & FN & " := ");

            if Has_Default_Value (FI, BK) then
               P (O, Default_Value (FI, BK));
            else
               P (O, Param_Name (FI));
            end if;

            PL (O, ";");

         elsif BK = Builder_Regular then
            P (O, New_Node & "." & FN & " := ");
            P (O, Param_Name (FI));
            PL (O, ";");

         else
            if Is_List (FI) then
               PL (O, "declare");
               Relative_Indent (O, 3);
               PL (O, "use Node_Lists;");
               NL (O);
               PL (O, "Nodes    : constant List := "
                  & "Get_List (" & Param_Name (FI) & ");");
               PL (O, "Position : Cursor := First (Nodes);");
               PL (O, "NL       : constant Why_Node_List := New_List;");
               Relative_Indent (O, -3);

               PL (O, "begin");
               Relative_Indent (O, 3);
               PL (O, "while Position /= No_Element loop");
               Relative_Indent (O, 3);

               PL (O, "declare");
               Relative_Indent (O, 3);
               PL (O, "Node : constant " & Unchecked_Element_Type_Name (FI)
                   & " := Element (Position);");
               Relative_Indent (O, -3);
               PL (O, "begin");
               Relative_Indent (O, 3);
               PL (O, List_Op_Name (Op_Append) & " (NL,  Node);");
               Relative_Indent (O, -3);
               PL (O, "end;");

               PL (O, "Position := Next (Position);");
               Relative_Indent (O, -3);
               PL (O, "end loop;");
               PL (O, New_Node & "." & FN & " := NL;");
               Relative_Indent (O, -3);
               PL (O, "end;");

            elsif not Is_Why_Id (FI) then
               P (O, New_Node & "." & FN & " := ");
               P (O, Param_Name (FI));
               PL (O, ";");

            else
               if Maybe_Null (FI) then
                  PL (O, "if " & Param_Name (FI) & " = Why_Empty then");
                  Relative_Indent (O, 3);
                  PL (O, New_Node & "." & FN & " := Why_Empty;");
                  Relative_Indent (O, -3);

                  PL (O, "else");
                  Relative_Indent (O, 3);
               end if;

               PL (O, New_Node & "." & FN & " :=");
               Relative_Indent (O, 2);
               PL (O, Builder_Name (Field_Kind (FI), Builder_Copy));
               PL (O, "(Id => " & Param_Name (FI) & ");");
               Relative_Indent (O, -2);

               if Maybe_Null (FI) then
                  Relative_Indent (O, -3);
                  PL (O, "end if;");
               end if;
            end if;
         end if;
      end Print_Record_Initialization;

   begin
      Common_Fields.Fields.Iterate (Print_Record_Initialization'Access);
      Variant_Part.Fields.Iterate (Print_Record_Initialization'Access);

      for SF in Special_Fields'Range loop
         case SF is
            when Special_Field_Checked =>
               P (O, New_Node & "." & To_String (SF) & " := ");

               if BK = Builder_Unchecked then
                  PL (O, "False;");
               else
                  PL (O, "True;");
               end if;

            when Special_Field_Link =>
               PL (O, New_Node & "." & To_String (SF) & " := Why_Empty;");

            when others =>
               --  All special fields should be initialized
               pragma Assert (False);
         end case;
      end loop;

      PL (O, "return New_Why_Node_Id (" & New_Node & ");");
   end Print_Builder_Implementation;

   --------------------------------------
   -- Print_Builder_Local_Declarations --
   --------------------------------------

   procedure Print_Builder_Local_Declarations
     (O    : in out Output_Record;
      Kind : Why_Node_Kind;
      BK   : Builder_Kind)
   is
      use Node_Lists;

      Variant_Part  : constant Why_Node_Info :=
                        Why_Tree_Info (Kind);
      Max_Param_Len : Natural;

      procedure Print_Variable_Declaration (Position : Cursor);

      --------------------------------
      -- Print_Variable_Declaration --
      --------------------------------

      procedure Print_Variable_Declaration (Position : Cursor)
      is
         Name_Len : Natural;
         FI       : constant Field_Info := Element (Position);
         PN       : constant Wide_String := Param_Name (FI);
      begin
         P (O, PN);
         Name_Len := PN'Length;

         --  Align columns

         if BK = Builder_Unchecked then
            P (O, " ");
         else
            Adjust_Columns (O, Name_Len, Max_Param_Len);
         end if;

         P (O, ": constant ");
         P (O, Id_Type_Name (FI));

         PL (O, " :=");
         Relative_Indent (O, 3);
         P (O, Accessor_Name (Kind, FI));
         PL (O, " (" & Node_Id_Param & ");");
         Relative_Indent (O, -3);
      end Print_Variable_Declaration;

   --  Start of processing for Print_Builder_Specification

   begin
      PL (O, New_Node & " : Why_Node (" & Mixed_Case_Name (Kind)  & ");");

      if BK /= Builder_Copy then
         return;
      end if;

      Max_Param_Len := Max_Param_Length (Kind, False);
      Variant_Part.Fields.Iterate (Print_Variable_Declaration'Access);
   end Print_Builder_Local_Declarations;

   ---------------------------------
   -- Print_Builder_Specification --
   ---------------------------------

   procedure Print_Builder_Specification
     (O    : in out Output_Record;
      Kind : Why_Node_Kind;
      BK   : Builder_Kind)
   is
      use Node_Lists;

      Variant_Part  : constant Why_Node_Info :=
                        Why_Tree_Info (Kind);
      Max_Param_Len : Natural;
      Field_Number  : Positive := 1;

      procedure Print_Parameter_Specification (Position : Cursor);

      procedure Print_Id_Parameter_Specification;

      --------------------------------------
      -- Print_Id_Parameter_Specification --
      --------------------------------------

      procedure Print_Id_Parameter_Specification is
      begin
         PL (O, ";");
         P (O, Node_Id_Param);
         Adjust_Columns (O, Node_Id_Param'Length, Max_Param_Len);
         P (O, ": ");
         P (O, Id_Subtype (Mixed_Case_Name (Kind), Regular, Id_Lone));
      end Print_Id_Parameter_Specification;

      -----------------------------------
      -- Print_Parameter_Specification --
      -----------------------------------

      procedure Print_Parameter_Specification (Position : Cursor)
      is
         Name_Len : Natural;
         FI       : constant Field_Info := Element (Position);
         PN       : constant Wide_String := Param_Name (FI);
      begin
         if BK = Builder_Unchecked then
            if Has_Default_Value (FI, BK) then
               return;
            end if;
         end if;

         if Field_Number = 1 then
            P (O, "(");
            Relative_Indent (O, 1);
         else
            PL (O, ";");
         end if;

         P (O, PN);
         Name_Len := PN'Length;

         --  Align columns

         if BK = Builder_Unchecked then
            P (O, " ");
         else
            Adjust_Columns (O, Name_Len, Max_Param_Len);
         end if;

         P (O, ": ");
         P (O, Id_Type_Name (FI));

         if Has_Default_Value (FI) then
            P (O, " := ");
            P (O, Default_Value (FI));
         end if;

         Field_Number := Field_Number + 1;
      end Print_Parameter_Specification;

   --  Start of processing for Print_Builder_Specification

   begin
      if BK = Builder_Copy then
         Max_Param_Len := Common_Fields.Max_Field_Name_Length;
      else
         Max_Param_Len := Max_Param_Length (Kind);
      end if;

      PL (O, "function " & Builder_Name (Kind, BK));
      Relative_Indent (O, 2);

      Common_Fields.Fields.Iterate (Print_Parameter_Specification'Access);

      if BK = Builder_Copy then
         Print_Id_Parameter_Specification;
      else
         Variant_Part.Fields.Iterate (Print_Parameter_Specification'Access);
      end if;

      if Field_Number > 1 then
         PL (O, ")");
         Relative_Indent (O, -1);
      end if;

      if BK = Builder_Unchecked then
         P (O, "return " & Unchecked_Id_Type_Name (Kind));
      else
         P (O, "return " & Id_Type_Name (Kind));
      end if;

      Relative_Indent (O, -2);
   end Print_Builder_Specification;

   ---------------------------------
   -- Print_Builder_Postcondition --
   ---------------------------------

   procedure Print_Builder_Postcondition
     (O    : in out Output_Record;
      Kind : Why_Node_Kind;
      BK   : Builder_Kind)
   is
      use Node_Lists;

      Variant_Part  : constant Why_Node_Info :=
                        Why_Tree_Info (Kind);

      procedure Print_Parameter_Postcondition (Position : Cursor);

      -----------------------------------
      -- Print_Parameter_Postcondition --
      -----------------------------------

      procedure Print_Parameter_Postcondition (Position : Cursor) is
         FI : constant Field_Info := Element (Position);
         PN : constant Wide_String := Param_Name (FI);
      begin
         PL (O, "and then");
         PL (O, "  " &  Accessor_Name (Kind, FI));
         PL (O, "  (" & Builder_Name (Kind, BK)
             & "'Result)");
         P  (O, "  = " & PN);

         if Next (Position) /= No_Element then
            NL (O);
         end if;
      end Print_Parameter_Postcondition;

   begin
      PL (O, "pragma Postcondition");
      Relative_Indent (O, 2);
      PL (O, "(Get_Kind");
      PL (O, "  (" & Builder_Name (Kind, BK) & "'Result)");
      PL (O, "  = " & Mixed_Case_Name (Kind));

      if BK /= Builder_Unchecked then
         Relative_Indent (O, 1);
         Common_Fields.Fields.Iterate (Print_Parameter_Postcondition'Access);

         if Has_Variant_Part (Kind) and then BK = Builder_Regular then
            NL (O);
            Variant_Part.Fields.Iterate (Print_Parameter_Postcondition'Access);
         end if;

         Relative_Indent (O, -1);
      end if;

      PL (O, ");");
      Relative_Indent (O, -2);
   end Print_Builder_Postcondition;

   --------------------------------
   -- Print_Builder_Precondition --
   --------------------------------

   procedure Print_Builder_Precondition
     (O    : in out Output_Record;
      Kind : Why_Node_Kind;
      BK   : Builder_Kind)
   is
      use Node_Lists;

      Variant_Part  : constant Why_Node_Info :=
                        Why_Tree_Info (Kind);

      procedure Print_Parameter_Precondition (Position : Cursor);

      procedure Print_Id_Parameter_Precondition;

      -------------------------------------
      -- Print_Id_Parameter_Precondition --
      -------------------------------------

      procedure Print_Id_Parameter_Precondition is
      begin
         P (O, Tree_Check (Mixed_Case_Name (Kind), Id_One));
         P (O, " (" & Node_Id_Param & ")");
      end Print_Id_Parameter_Precondition;

      ----------------------------------
      -- Print_Parameter_Precondition --
      ----------------------------------

      procedure Print_Parameter_Precondition (Position : Cursor) is
         FI : constant Field_Info := Element (Position);
         PN : constant Wide_String := Param_Name (FI);
      begin
         if Is_Why_Id (FI) then
            P (O, Tree_Check (Field_Kind (FI), Multiplicity (FI)));
            P (O, " (" & PN & ")");
         else
            P (O, "True");
         end if;

         if Previous (Position) = No_Element then
            Relative_Indent (O, 1);
         end if;

         if Next (Position) /= No_Element then
            NL (O);
            P (O, "and then ");
         else
            Relative_Indent (O, -1);
         end if;
      end Print_Parameter_Precondition;

   begin
      if (Has_Variant_Part (Kind)
          and then BK = Builder_Regular)
        or else BK = Builder_Copy
      then
         PL (O, "pragma Precondition");
         Relative_Indent (O, 2);
         P (O, "(");

         if BK = Builder_Regular then
            Variant_Part.Fields.Iterate (Print_Parameter_Precondition'Access);
         else
            Print_Id_Parameter_Precondition;
         end if;

         PL (O, ");");
         Relative_Indent (O, -2);
      end if;
   end Print_Builder_Precondition;

   -------------------------------------
   -- Print_Class_Copy_Builder_Bodies --
   -------------------------------------

   procedure Print_Class_Copy_Builder_Bodies
     (O : in out Output_Record)
   is
      use Class_Lists;

      procedure Process_One_Class_Kind (Position : Class_Lists.Cursor);

      ----------------------------
      -- Process_One_Class_Kind --
      ----------------------------

      procedure Process_One_Class_Kind (Position : Class_Lists.Cursor) is
         CI : constant Class_Info := Class_Lists.Element (Position);
      begin
         Print_Class_Copy_Builder_Body (O, CI);

         if Position /= Classes.Last then
            NL (O);
         end if;
      end Process_One_Class_Kind;

   begin
      Classes.Iterate (Process_One_Class_Kind'Access);
   end Print_Class_Copy_Builder_Bodies;

   -----------------------------------
   -- Print_Class_Copy_Builder_Body --
   -----------------------------------

   procedure Print_Class_Copy_Builder_Body
     (O  : in out Output_Record;
      CI : Class_Info)
   is
      Max_Param_Len : constant Natural := Common_Fields.Max_Field_Name_Length;

      procedure Print_Kind_Expression
        (O    : in out Output_Record;
         Kind : Why_Node_Kind);

      ---------------------------
      -- Print_Kind_Expression --
      ---------------------------

      procedure Print_Kind_Expression
        (O    : in out Output_Record;
         Kind : Why_Node_Kind)
      is
         use Node_Lists;

         procedure Print_Field_Component_Choice (Position : Cursor);
         procedure Print_Component_Choice (PN : Wide_String);

         ----------------------------
         -- Print_Component_Choice --
         ----------------------------

         procedure Print_Component_Choice (PN : Wide_String) is
         begin
            P (O, PN);
            Adjust_Columns (O, PN'Length, Max_Param_Len);
            P (O, " => " & PN);
         end;

         ----------------------------------
         -- Print_Field_Component_Choice --
         ----------------------------------

         procedure Print_Field_Component_Choice (Position : Cursor) is
            FI : constant Field_Info := Element (Position);
            PN : constant Wide_String := Param_Name (FI);
         begin
            Print_Component_Choice (PN);
            PL (O, ",");
         end Print_Field_Component_Choice;

      begin
         PL (O, Builder_Name (Kind, Builder_Copy));
         P (O, " (");
         Relative_Indent (O, 2);
         Common_Fields.Fields.Iterate (Print_Field_Component_Choice'Access);
         Print_Component_Choice (Node_Id_Param);
         P (O, ")");
         Relative_Indent (O, -2);
      end Print_Kind_Expression;

   begin
      Print_Class_Copy_Builder_Specification (O, Class_Name (CI));
      PL (O, " is");
      Relative_Indent (O, 2);
      Print_Class_Case_Expression (O, CI, Node_Id_Param, "Why_Empty",
                                   Print_Kind_Expression'Access);
      Relative_Indent (O, -2);
      NL (O);
   end Print_Class_Copy_Builder_Body;

   -------------------------------------------
   -- Print_Class_Copy_Builder_Declarations --
   -------------------------------------------

   procedure Print_Class_Copy_Builder_Declarations
     (O : in out Output_Record)
   is
      use Class_Lists;

      procedure Process_One_Class_Kind (Position : Class_Lists.Cursor);

      ----------------------------
      -- Process_One_Class_Kind --
      ----------------------------

      procedure Process_One_Class_Kind (Position : Class_Lists.Cursor) is
         CI : constant Class_Info := Class_Lists.Element (Position);
      begin
         Print_Class_Copy_Builder_Declaration (O, Class_Name (CI));

         if Position /= Classes.Last then
            NL (O);
         end if;
      end Process_One_Class_Kind;

   begin
      Classes.Iterate (Process_One_Class_Kind'Access);
   end Print_Class_Copy_Builder_Declarations;

   ------------------------------------------
   -- Print_Class_Copy_Builder_Declaration --
   ------------------------------------------

   procedure Print_Class_Copy_Builder_Declaration
     (O      : in out Output_Record;
      Prefix : Wide_String)
   is
   begin
      Print_Class_Copy_Builder_Specification (O, Prefix);
      PL (O, ";");
   end Print_Class_Copy_Builder_Declaration;

   --------------------------------------------
   -- Print_Class_Copy_Builder_Specification --
   --------------------------------------------

   procedure Print_Class_Copy_Builder_Specification
     (O      : in out Output_Record;
      Prefix : Wide_String)
   is
      use Node_Lists;

      Max_Param_Len : Natural;
      Field_Number  : Positive := 1;

      procedure Print_Parameter_Specification (Position : Cursor);

      procedure Print_Id_Parameter_Specification;

      --------------------------------------
      -- Print_Id_Parameter_Specification --
      --------------------------------------

      procedure Print_Id_Parameter_Specification is
      begin
         P (O, Node_Id_Param);
         Adjust_Columns (O, Node_Id_Param'Length, Max_Param_Len);
         P (O, ": ");
         P (O, Id_Type_Name (Prefix));
      end Print_Id_Parameter_Specification;

      -----------------------------------
      -- Print_Parameter_Specification --
      -----------------------------------

      procedure Print_Parameter_Specification (Position : Cursor)
      is
         Name_Len : Natural;
         FI       : constant Field_Info := Element (Position);
         PN       : constant Wide_String := Param_Name (FI);
      begin
         P (O, PN);
         Name_Len := PN'Length;
         Adjust_Columns (O, Name_Len, Max_Param_Len);

         P (O, ": ");
         P (O, Id_Type_Name (FI));

         if Has_Default_Value (FI) then
            P (O, " := ");
            P (O, Default_Value (FI));
         end if;

         PL (O, ";");
      end Print_Parameter_Specification;

   --  Start of processing for Print_Class_Copy_Builder_Specification

   begin
      Max_Param_Len := Common_Fields.Max_Field_Name_Length;

      PL (O, "function " & Builder_Name (Prefix, Builder_Copy));
      Relative_Indent (O, 2);

      P (O, "(");
      Relative_Indent (O, 1);
      Common_Fields.Fields.Iterate (Print_Parameter_Specification'Access);
      Print_Id_Parameter_Specification;
      PL (O, ")");
      Relative_Indent (O, -1);
      P (O, "return " & Id_Type_Name (Prefix));
      Relative_Indent (O, -2);
   end Print_Class_Copy_Builder_Specification;

   -------------------------------
   -- Print_Copy_Builder_Bodies --
   -------------------------------

   procedure Print_Copy_Builder_Bodies (O : in out Output_Record) is
   begin
      for J in Valid_Kind'Range loop
         Print_Builder_Body (O, J, Builder_Copy);

         if J /= Why_Tree_Info'Last then
            NL (O);
         end if;
      end loop;
   end Print_Copy_Builder_Bodies;

   -------------------------------------
   -- Print_Copy_Builder_Declarations --
   -------------------------------------

   procedure Print_Copy_Builder_Declarations
     (O  : in out Output_Record)
   is
   begin
      for J in Valid_Kind'Range loop
         Print_Builder_Declaration (O, J, Builder_Copy);

         if J /= Why_Tree_Info'Last then
            NL (O);
         end if;
      end loop;
   end Print_Copy_Builder_Declarations;

   ------------------------------------
   -- Print_Unchecked_Builder_Bodies --
   ------------------------------------

   procedure Print_Unchecked_Builder_Bodies (O : in out Output_Record) is
   begin
      for J in Valid_Kind'Range loop
         Print_Builder_Body (O, J, Builder_Unchecked);

         if J /= Why_Tree_Info'Last then
            NL (O);
         end if;
      end loop;
   end Print_Unchecked_Builder_Bodies;

   ------------------------------------------
   -- Print_Unchecked_Builder_Declarations --
   ------------------------------------------

   procedure Print_Unchecked_Builder_Declarations
     (O  : in out Output_Record)
   is
   begin
      for J in Valid_Kind'Range loop
         Print_Builder_Declaration (O, J, Builder_Unchecked);

         if J /= Why_Tree_Info'Last then
            NL (O);
         end if;
      end loop;
   end Print_Unchecked_Builder_Declarations;

end Xtree_Builders;
