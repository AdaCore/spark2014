------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                               X K I N D S                                --
--                                                                          --
--                                 B o d y                                  --
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

with Ada.Wide_Text_IO;           use Ada.Wide_Text_IO;
with Ada.Strings;                use Ada.Strings;
with Ada.Strings.Wide_Fixed;     use Ada.Strings.Wide_Fixed;

with Asis;                       use Asis;
with Asis.Implementation;        use Asis.Implementation;
with Asis.Ada_Environments;      use Asis.Ada_Environments;
with Asis.Compilation_Units;     use Asis.Compilation_Units;
with Asis.Iterator;              use Asis.Iterator;
with Asis.Elements;              use Asis.Elements;
with Asis.Text;                  use Asis.Text;
with Asis.Extensions.Flat_Kinds; use Asis.Extensions.Flat_Kinds;

procedure Xkinds is
   --  ASIS helper that takes Why.Sinfo's syntax tree and generates a list
   --  of subtypes of Why_Node_Id, one per kind (and will also generate
   --  a subtype predicate when GNAT will support them). Same thing for
   --  node classes.

   My_Context : Asis.Context;

   type Traversal_State is
     (Before_Why_Node_Kind,
      In_Why_Node_Kind,
      After_Why_Node_Kind,
      In_Why_Node_Class_Declaration);

   procedure Pre_Operation
     (Element :        Asis.Element;
      Control : in out Asis.Traverse_Control;
      State   : in out Traversal_State);

   procedure Post_Operation
     (Element :        Asis.Element;
      Control : in out Asis.Traverse_Control;
      State   : in out Traversal_State);

   procedure Traverse_Source is new Asis.Iterator.Traverse_Element
     (State_Information => Traversal_State);

   procedure Print_Subtype (S : Wide_String);

   -------------------
   -- Pre_Operation --
   -------------------

   procedure Pre_Operation
     (Element :        Asis.Element;
      Control : in out Asis.Traverse_Control;
      State   : in out Traversal_State)
   is
      pragma Unreferenced (Control);

      Kind : constant Flat_Element_Kinds := Flat_Element_Kind (Element);
   begin
      case State is
         when Before_Why_Node_Kind =>
            if Kind = A_Defining_Identifier then
               declare
                  Text : constant Asis.Program_Text :=
                           Trim (Asis.Text.Element_Image (Element), Both);
               begin
                  if Text = "Why_Node_Kind" then
                     State := In_Why_Node_Kind;
                  end if;
               end;
            end if;

         when In_Why_Node_Kind =>
            if Kind = A_Defining_Enumeration_Literal then
               declare
                  Text : constant Asis.Program_Text :=
                           Trim (Asis.Text.Element_Image (Element), Both);
               begin
                  Print_Subtype (Text);
                  New_Line;
               end;
            end if;

         when In_Why_Node_Class_Declaration =>
            if Kind = A_Defining_Identifier then
               declare
                  Text : constant Asis.Program_Text :=
                           Trim (Asis.Text.Element_Image (Element), Both);
               begin
                  Print_Subtype (Text);
                  New_Line;
               end;
            end if;

         when After_Why_Node_Kind =>
            if Kind = A_Subtype_Declaration then
               State := In_Why_Node_Class_Declaration;
            end if;

      end case;
   end Pre_Operation;

   --------------------
   -- Post_Operation --
   --------------------

   procedure Post_Operation
     (Element :        Asis.Element;
      Control : in out Asis.Traverse_Control;
      State   : in out Traversal_State)
   is
      pragma Unreferenced (Control);

      Kind : constant Flat_Element_Kinds := Flat_Element_Kind (Element);
   begin
      case State is
         when Before_Why_Node_Kind =>
            null;

         when In_Why_Node_Kind =>
            if Kind = An_Enumeration_Type_Definition then
               State := After_Why_Node_Kind;
            end if;

         when In_Why_Node_Class_Declaration =>
            if Kind = A_Subtype_Declaration then
               State := After_Why_Node_Kind;
            end if;

         when After_Why_Node_Kind =>
            null;
      end case;
   end Post_Operation;

   -------------------
   -- Print_Subtype --
   -------------------

   procedure Print_Subtype (S : Wide_String) is
   begin
      Put_Line ("   subtype " & S & "_Id is Why_Node_Id;");
   end Print_Subtype;

   Control : Traverse_Control := Continue;
   State   : Traversal_State := Before_Why_Node_Kind;
begin
   Implementation.Initialize ("-ws");
   Ada_Environments.Associate
    (My_Context, "My Asis Context", "-C1 ./why-sinfo.adt");
   Ada_Environments.Open (My_Context);

   Processing_Units : declare
      Next_Unit : Compilation_Unit;
      All_Units : constant Compilation_Unit_List :=
                    Asis.Compilation_Units.Compilation_Units (My_Context);
   begin
      for I in All_Units'Range loop
         Next_Unit := All_Units (I);

         if Unit_Origin (Next_Unit) = An_Application_Unit then
            Traverse_Source (Unit_Declaration (Next_Unit),
                             Control,
                             State);
         end if;
      end loop;
   end Processing_Units;

   Close (My_Context);
   Dissociate (My_Context);
   Finalize;
end Xkinds;
