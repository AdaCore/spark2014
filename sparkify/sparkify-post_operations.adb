------------------------------------------------------------------------------
--                                                                          --
--                            SPARKIFY COMPONENTS                           --
--                                                                          --
--               S P A R K I F Y . P O S T _ O P E R A T I O N S            --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                     Copyright (C) 2009-2010, AdaCore                     --
--                                                                          --
-- Sparkify is  free  software;  you can redistribute it  and/or  modify it --
-- under terms of the  GNU General Public License as published  by the Free --
-- Software Foundation;  either version  2,  or  (at your option) any later --
-- version. Sparkify is distributed in the hope that it will be useful, but --
-- WITHOUT ANY WARRANTY; without even the implied warranty of  MERCHANTABI- --
-- LITY or  FITNESS  FOR A  PARTICULAR  PURPOSE. See the GNU General Public --
-- License  for more details. You  should  have  received a copy of the GNU --
-- General Public License  distributed with GNAT; see file COPYING. If not, --
-- write to the Free Software Foundation,  51 Franklin Street, Fifth Floor, --
-- Boston,                                                                  --
--                                                                          --
-- Sparkify is maintained by AdaCore (http://www.adacore.com)               --
--                                                                          --
------------------------------------------------------------------------------

with Ada.Characters.Conversions;       use Ada.Characters.Conversions;

with Asis.Extensions;                  use Asis.Extensions;
with Asis.Declarations;                use Asis.Declarations;
with Asis.Text;                        use Asis.Text;
with Asis.Elements;                    use Asis.Elements;

with Sparkify.PP_Output;               use Sparkify.PP_Output;
with Sparkify.Cursors;                 use Sparkify.Cursors;
with Sparkify.Names;                   use Sparkify.Names;

package body Sparkify.Post_Operations is

   -------------------------------------------
   -- A_Package_Declaration_Or_Body_Post_Op --
   -------------------------------------------

   procedure A_Package_Declaration_Or_Body_Post_Op
     (Element :        Asis.Element;
      Control : in out Traverse_Control;
      State   : in out Source_Traversal_State)
   is
      pragma Unreferenced (Control);

      Last_Element : Asis.Element;

      Name : constant Wide_String :=
               Flat_Package_Name (Declaration_Unique_Name (Element));
   begin
      if Declaration_Kind (Element) = A_Package_Declaration then
         declare
            Items : constant Declarative_Item_List :=
              Private_Part_Declarative_Items (Declaration     => Element,
                                              Include_Pragmas => True);
         begin
            if Items'Length = 0 then
               declare
                  Items : constant Declarative_Item_List :=
                    Visible_Part_Declarative_Items (Declaration     => Element,
                                                    Include_Pragmas => True);
               begin
                  pragma Assert (Items'Length > 0);
                  Last_Element := Items (Items'Last);
               end;
            else
               pragma Assert (Items'Length > 0);
               Last_Element := Items (Items'Last);
            end if;
         end;
      else
         pragma Assert
           (Declaration_Kind (Element) = A_Package_Body_Declaration);
         declare
            Statements : constant Statement_List :=
              Body_Statements (Declaration     => Element,
                               Include_Pragmas => True);
         begin
            if Statements'Length = 0 then
               declare
                  Items : constant Declarative_Item_List :=
                    Body_Declarative_Items (Declaration     => Element,
                                            Include_Pragmas => True);
               begin
                  pragma Assert (Items'Length > 0);
                  Last_Element := Items (Items'Last);
               end;
            else
               pragma Assert (Statements'Length > 0);
               Last_Element := Statements (Statements'Last);
            end if;
         end;
      end if;

      declare
         Last_Line_Cursor : constant Cursor :=
           Line_Cursor (Before_Line, Last_Line_Number (Element));
         --  In order to get both the last package item and the last comment,
         --  the last cursor should be positioned as the maximum of the cursor
         --  at the end of the last item and the cursor at the beginning of
         --  the last line.
         Last_Cursor : constant Cursor :=
           Max_Cursor (Cursor_At_End_Of (Last_Element), Last_Line_Cursor);
      begin
         PP_Echo_Cursor_Range (State.Echo_Cursor, Last_Cursor);
         PP_Text_At (Line   => Last_Line_Number (Element),
                     Column => Element_Span (Element).First_Column,
                     Text   => "end ");

         if Current_Pass = Printing_Internal then
            --  Prefix the name of the package to differentiate it
            PP_Word (To_Wide_String (Internal_Prefix));
         end if;

         PP_Word (Name & ";");
         State.Echo_Cursor := Cursor_After (Element);
      end;
   end A_Package_Declaration_Or_Body_Post_Op;

   -------------------------------
   -- A_Subprogram_Unit_Post_Op --
   -------------------------------

   procedure A_Subprogram_Unit_Post_Op
     (Element :        Asis.Element;
      Control : in out Traverse_Control;
      State   : in out Source_Traversal_State)
   is
      pragma Unreferenced (Control);

      Statements : constant Statement_List :=
         Body_Statements (Declaration     => Element,
                          Include_Pragmas => True);
      pragma Assert (Statements'Length > 0);
      Last_Statement : constant Statement := Statements (Statements'Last);
      Last_Line_Cursor : constant Cursor :=
        Line_Cursor (Before_Line, Last_Line_Number (Element));
      --  In order to get both the last statement and the last comment,
      --  the last cursor should be positioned as the maximum of the cursor at
      --  the end of the last statement and the cursor at the beginning of
      --  the last line.
      Last_Cursor : constant Cursor :=
         Max_Cursor (Cursor_At_End_Of (Last_Statement), Last_Line_Cursor);

      Name : constant Wide_String := Declaration_Unique_Name (Element);
   begin
      PP_Echo_Cursor_Range (State.Echo_Cursor, Last_Cursor);
      PP_Text_At (Line   => Last_Line_Number (Element),
                  Column => Element_Span (Element).First_Column,
                  Text   => "end " & Name & ";");
      State.Echo_Cursor := Cursor_After (Element);
   end A_Subprogram_Unit_Post_Op;

end Sparkify.Post_Operations;
