with Ada.Containers; use Ada.Containers;
with Why.Sinfo; use Why.Sinfo;

package body Xtree_Builders is

   procedure Print_Builder_Declaration
     (O    : in out Output_Record;
      Kind : Why_Node_Kind);

   procedure Print_Builder_Specification
     (O    : in out Output_Record;
      Kind : Why_Node_Kind);

   --------------------
   -- Print_Builders --
   --------------------

   procedure Print_Builders
     (O  : in out Output_Record)
   is
   begin
      for J in Why_Tree_Info'Range loop
         Print_Builder_Declaration (O, J);
      end loop;
   end Print_Builders;

   -------------------------------
   -- Print_Builder_Declaration --
   -------------------------------

   procedure Print_Builder_Declaration
     (O    : in out Output_Record;
      Kind : Why_Node_Kind) is
   begin
      Print_Builder_Specification (O, Kind);
      PL (O, ";");
      NL (O);
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
      In_Variant    : Boolean := False;

      procedure Print_Parameter_Specification (Position : Cursor);

      -----------------------------------
      -- Print_Parameter_Specification --
      -----------------------------------

      procedure Print_Parameter_Specification (Position : Cursor)
      is
         Name_Len : Natural;
         FI       : constant Field_Info := Element (Position);
      begin
         if Field_Number = 1 then
            P (O, "(");
            Relative_Indent (O, 1);
         else
            PL (O, ";");
         end if;

         if In_Variant then
            declare
               PN : constant Wide_String := Param_Name (FI.Field_Name.all);
            begin
               P (O, PN);
               Name_Len := PN'Length;
            end;
         else
            P (O, FI.Field_Name.all);
            Name_Len := FI.Field_Name'Length;
         end if;

         --  Align columns

         for J in Name_Len .. Max_Param_Len loop
            P (O, " ");
         end loop;
         P (O, " : ");

         P (O, FI.Field_Type.all);
         Field_Number := Field_Number + 1;
      end Print_Parameter_Specification;

   begin
      PL (O, "function " & Builder_Name (Kind));
      Relative_Indent (O, 2);
      Common_Fields.Fields.Iterate (Print_Parameter_Specification'Access);
      In_Variant := True;
      Variant_Part.Fields.Iterate (Print_Parameter_Specification'Access);
      PL (O, ")");
      Relative_Indent (O, -1);
      P (O, "return " & Id_Type_Name (Kind));
      Relative_Indent (O, -2);
   end Print_Builder_Specification;

   ------------------
   -- Print_Fields --
   ------------------

   procedure Print_Fields
     (O  : in out Output_Record;
      NI : Why_Node_Info)
   is
      use Node_Lists;

      procedure Print_Field (Position : Cursor);

      -----------------
      -- Print_Field --
      -----------------

      procedure Print_Field (Position : Cursor) is
         FI : constant Field_Info := Element (Position);
      begin
         P (O, FI.Field_Name.all);

         --  Align columns

         for J in FI.Field_Name'Length .. NI.Max_Field_Name_Length loop
            P (O, " ");
         end loop;
         P (O, " : ");

         PL (O, FI.Field_Type.all);
      end Print_Field;

   begin
      if NI.Fields.Length = 0 then
         PL (O, "null;");
      else
         NI.Fields.Iterate (Print_Field'Access);
      end if;
   end Print_Fields;

end Xtree_Builders;
