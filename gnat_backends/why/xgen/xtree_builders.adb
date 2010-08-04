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

   -------------------------------
   -- Print_Builder_Declaration --
   -------------------------------

   procedure Print_Builder_Declaration
     (O    : in out Output_Record;
      Kind : Why_Node_Kind) is
   begin
      Print_Builder_Specification (O, Kind);
      PL (O, ";");
   end Print_Builder_Declaration;

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
         P (O, " : ");

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

end Xtree_Builders;
