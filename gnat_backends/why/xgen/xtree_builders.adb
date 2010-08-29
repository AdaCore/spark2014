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

   type Builder_Kind is (Builder_Regular, Builder_Unchecked);
   --  Type of builder. Builder_Regular for building builders
   --  that return regular ids (to valid nodes); Builder_Unchecked
   --  for builders that returns unchecked ids (to kind-valid nodes).

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

   --------------------------
   -- Print_Builder_Bodies --
   --------------------------

   procedure Print_Builder_Bodies  (O : in out Output_Record) is
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
      BN : constant Wide_String := Builder_Name (Kind);
   begin
      Print_Box (O, BN);
      NL (O);

      Print_Builder_Specification (O, Kind, BK);
      NL (O);
      PL (O, "is");
      PL (O, "begin");
      Relative_Indent (O, 3);
      Print_Builder_Implementation (O, Kind, BK);
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

         if BK = Builder_Regular then
            P (O, Param_Name (FI));

         else
            if Is_List (FI) then
               P (O, "New_List");
            elsif Is_Why_Id (FI) then
               P (O, "Why_Empty");
            else
               if Id_Type_Name (FI) = "Node_Id" then
                  P (O, "Empty");
               elsif Id_Type_Name (FI) = "Why_Node_Id" then
                  P (O, "Why_Empty");
               else
                  P (O, Param_Name (FI));
               end if;
            end if;
         end if;

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

      for SF in Special_Fields'Range loop
         case SF is
            when Special_Field_Checked =>
               PL (O, ",");
               Print_Component_Choice (O, To_String (SF));

               if BK = Builder_Regular then
                  P (O, "True");
               else
                  P (O, "False");
               end if;

            when others =>
               --  All special fields should be initialized
               pragma Assert (False);
         end case;
      end loop;

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
      Kind : Why_Node_Kind;
      BK   : Builder_Kind)
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
         if BK = Builder_Unchecked then
            if Is_List (FI)
              or else Is_Why_Id (FI)
              or else Id_Type_Name (FI) = "Node_Id"
              or else Id_Type_Name (FI) = "Why_Node_Id" then
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

         if BK = Builder_Regular then
            for J in Name_Len .. Max_Param_Len loop
               P (O, " ");
            end loop;
         else
            P (O, " ");
         end if;

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

      if Field_Number > 1 then
         PL (O, ")");
         Relative_Indent (O, -1);
      end if;

      if BK = Builder_Regular then
         P (O, "return " & Id_Type_Name (Kind));
      else
         P (O, "return " & Unchecked_Id_Type_Name (Kind));
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
         PL (O, "  (" & Builder_Name (Kind) & "'Result)");
         P  (O, "  = " & PN);

         if Next (Position) /= No_Element then
            NL (O);
         end if;
      end Print_Parameter_Postcondition;

   begin
      PL (O, "pragma Postcondition");
      Relative_Indent (O, 2);
      PL (O, "(Get_Kind");
      PL (O, "  (" & Builder_Name (Kind) & "'Result)");
      PL (O, "  = " & Mixed_Case_Name (Kind));

      if BK = Builder_Regular then
         Relative_Indent (O, 1);
         Common_Fields.Fields.Iterate (Print_Parameter_Postcondition'Access);

         if Has_Variant_Part (Kind) then
            NL (O);
            Variant_Part.Fields.Iterate (Print_Parameter_Postcondition'Access);
         end if;
         Relative_Indent (O, -1);
      end if;

      PL (O, ");");
      Relative_Indent (O, -2);
   end Print_Builder_Postcondition;

   ------------------------------------
   -- Print_Unchecked_Builder_Bodies --
   ------------------------------------

   procedure Print_Unchecked_Builder_Bodies  (O : in out Output_Record) is
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
