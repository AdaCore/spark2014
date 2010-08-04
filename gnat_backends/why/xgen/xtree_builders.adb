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

with Why.Sinfo;    use Why.Sinfo;
with Xtree_Tables; use Xtree_Tables;

package body Xtree_Builders is

   procedure Print_Builder_Declaration
     (O    : in out Output_Record;
      Kind : Why_Node_Kind);
   --  Print builder declaration for the given node kind

   procedure Print_Builder_Specification
     (O    : in out Output_Record;
      Kind : Why_Node_Kind);
   --  Print builder specification for the given node kind

   procedure Print_Builder_Postcondition
     (O    : in out Output_Record;
      Kind : Why_Node_Kind);
   --  Print builder postcondition for the given node kind

   procedure Print_Builder_Body
     (O    : in out Output_Record;
      Kind : Why_Node_Kind);
   --  Print builder body for the given node kind

   procedure Print_Builder_Implementation
     (O    : in out Output_Record;
      Kind : Why_Node_Kind);
   --  Print the handled sequence of statements that implements this builder

   procedure Print_Box
     (O               : in out Output_Record;
      Subprogram_Name : Wide_String);

   --------------------------
   -- Print_Builder_Bodies --
   --------------------------

   procedure Print_Builder_Bodies  (O : in out Output_Record) is
   begin
      for J in Why_Tree_Info'Range loop
         Print_Builder_Body (O, J);

         if J /= Why_Tree_Info'Last then
            NL (O);
         end if;
      end loop;
   end Print_Builder_Bodies;

   ------------------------
   -- Print_Builder_Body --
   -------------------------

   procedure Print_Builder_Body
     (O    : in out Output_Record;
      Kind : Why_Node_Kind)
   is
      BN : constant Wide_String := Builder_Name (Kind);
   begin
      Print_Box (O, BN);
      NL (O);

      Print_Builder_Specification (O, Kind);
      NL (O);
      PL (O, "is");
      PL (O, "begin");
      Relative_Indent (O, 3);
      Print_Builder_Implementation (O, Kind);
      Relative_Indent (O, -3);
      PL (O, "end " & BN & ";");
   end Print_Builder_Body;

   --------------------------------
   -- Print_Builder_Declarations --
   --------------------------------

   procedure Print_Builder_Declarations
     (O  : in out Output_Record)
   is
   begin
      for J in Why_Tree_Info'Range loop
         Print_Builder_Declaration (O, J);

         if J /= Why_Tree_Info'Last then
            NL (O);
         end if;
      end loop;
   end Print_Builder_Declarations;

   ---------------
   -- Print_Box --
   ---------------

   procedure Print_Box
     (O               : in out Output_Record;
      Subprogram_Name : Wide_String)
   is
      procedure Print_Line;

      procedure Print_Line is
      begin
         P (O, "---");
         for J in Subprogram_Name'Range loop
            P (O, "-");
         end loop;
         PL (O, "---");
      end Print_Line;

   begin
      Print_Line;
      PL (O, "-- " & Subprogram_Name & " --");
      Print_Line;
   end Print_Box;

   -------------------------------
   -- Print_Builder_Declaration --
   -------------------------------

   procedure Print_Builder_Declaration
     (O    : in out Output_Record;
      Kind : Why_Node_Kind) is
   begin
      Print_Builder_Specification (O, Kind);
      PL (O, ";");
      Print_Builder_Postcondition (O, Kind);
   end Print_Builder_Declaration;

   ----------------------------------
   -- Print_Builder_Implementation --
   ----------------------------------

   procedure Print_Builder_Implementation
     (O    : in out Output_Record;
      Kind : Why_Node_Kind)
   is
      use Node_Lists;

      Max_FN_Len   : constant Natural := Max_Field_Name_Length (Kind);
      Variant_Part : constant Why_Node_Info := Why_Tree_Info (Kind);
      Qualifier    : constant Wide_String := "  (Why_Node'(";

      procedure Print_Record_Component_Association (Position : Cursor);

      procedure Print_Component_Choice
        (O      : in out Output_Record;
         Choice : Wide_String);

      ----------------------------
      -- Print_Component_Choice --
      ----------------------------

      procedure Print_Component_Choice
        (O      : in out Output_Record;
         Choice : Wide_String) is
      begin
         P (O, Choice);
         for J in Choice'Length .. Max_FN_Len loop
            P (O, " ");
         end loop;
         P (O, "=> ");
      end Print_Component_Choice;

      ----------------------------------------
      -- Print_Record_Component_Association --
      ----------------------------------------

      procedure Print_Record_Component_Association (Position : Cursor) is
         FI : constant Field_Info := Element (Position);
         FN : constant Wide_String := Field_Name (FI);
      begin
         Print_Component_Choice (O, FN);
         P (O, Param_Name (FI));

         if Next (Position) /= No_Element then
            PL (O, ",");
         end if;
      end Print_Record_Component_Association;

   begin
      PL (O, "return New_Why_Node_Id");
      P (O, Qualifier);
      Relative_Indent (O, Qualifier'Length);

      --  Print discriminant association

      Print_Component_Choice (O, "Kind");
      PL (O, Mixed_Case_Name (Kind) & ",");

      --  Print other components association

      Common_Fields.Fields.Iterate (Print_Record_Component_Association'Access);

      if Has_Variant_Part (Kind) then
         PL (O, ",");
         Variant_Part.Fields.Iterate
           (Print_Record_Component_Association'Access);
      end if;

      PL (O, "));");
      Relative_Indent (O, -Qualifier'Length);
   end Print_Builder_Implementation;

   ---------------------------------
   -- Print_Builder_Specification --
   ---------------------------------

   procedure Print_Builder_Specification
     (O    : in out Output_Record;
      Kind : Why_Node_Kind)
   is
      use Node_Lists;

      Variant_Part  : constant Why_Node_Info :=
                        Why_Tree_Info (Kind);
      Max_Param_Len : constant Natural := Max_Param_Length (Kind);
      Field_Number  : Positive := 1;

      procedure Print_Parameter_Specification (Position : Cursor);

      -----------------------------------
      -- Print_Parameter_Specification --
      -----------------------------------

      procedure Print_Parameter_Specification (Position : Cursor)
      is
         Name_Len : Natural;
         FI       : constant Field_Info := Element (Position);
         PN       : constant Wide_String := Param_Name (FI);
      begin
         if Field_Number = 1 then
            P (O, "(");
            Relative_Indent (O, 1);
         else
            PL (O, ";");
         end if;

         P (O, PN);
         Name_Len := PN'Length;

         --  Align columns

         for J in Name_Len .. Max_Param_Len loop
            P (O, " ");
         end loop;
         P (O, ": ");

         P (O, Id_Type_Name (FI));
         Field_Number := Field_Number + 1;
      end Print_Parameter_Specification;

   --  Start of processing for Print_Builder_Specification

   begin
      PL (O, "function " & Builder_Name (Kind));
      Relative_Indent (O, 2);
      Common_Fields.Fields.Iterate (Print_Parameter_Specification'Access);
      Variant_Part.Fields.Iterate (Print_Parameter_Specification'Access);
      PL (O, ")");
      Relative_Indent (O, -1);
      P (O, "return " & Id_Type_Name (Kind));
      Relative_Indent (O, -2);
   end Print_Builder_Specification;

   ---------------------------------
   -- Print_Builder_Postcondition --
   ---------------------------------

   procedure Print_Builder_Postcondition
     (O    : in out Output_Record;
      Kind : Why_Node_Kind)
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
         PL (O, "and then " & Accessor_Name (Kind, FI));
         P (O, "  (" & Builder_Name (Kind) & "'Result)" & " = " & PN);

         if Next (Position) /= No_Element then
            NL (O);
         end if;
      end Print_Parameter_Postcondition;

   begin
      PL (O, "pragma Postcondition");
      Relative_Indent (O, 2);
      PL (O, "(Get_Kind");
      PL (O, "  (" & Builder_Name (Kind) & "'Result)"
          & " = " & Mixed_Case_Name (Kind));
      Relative_Indent (O, 1);
      Common_Fields.Fields.Iterate (Print_Parameter_Postcondition'Access);

      if Has_Variant_Part (Kind) then
         NL (O);
         Variant_Part.Fields.Iterate (Print_Parameter_Postcondition'Access);
      end if;
      Relative_Indent (O, -1);
      PL (O, ");");
      Relative_Indent (O, -2);
   end Print_Builder_Postcondition;

end Xtree_Builders;
