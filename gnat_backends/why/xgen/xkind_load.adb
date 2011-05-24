------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                           X K I N D _ L O A D                            --
--                                                                          --
--                                 B o d y                                  --
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

with Asis;                       use Asis;
with Asis.Implementation;        use Asis.Implementation;
with Asis.Ada_Environments;      use Asis.Ada_Environments;
with Asis.Compilation_Units;     use Asis.Compilation_Units;
with Asis.Iterator;              use Asis.Iterator;
with Asis.Elements;              use Asis.Elements;
with Asis.Declarations;          use Asis.Declarations;
with Asis.Definitions;           use Asis.Definitions;
with Asis.Extensions.Flat_Kinds; use Asis.Extensions.Flat_Kinds;
with Xkind_Tables;               use Xkind_Tables;
with Utils;                      use Utils;

package body Xkind_Load is

   My_Context : Asis.Context;

   type Traversal_State is
     (Before_Why_Node_Kind,
      In_Why_Node_Kind,
      After_Why_Node_Kind);
   --  The traversal of the syntax tree is implemented as a state machine
   --  whose states are defined by this enumeration and whose transitions
   --  are triggered by the detection of some Ada entities. See the
   --  case statements in Pre_Operation/Post_Operation for more details
   --  about these states and transitions.

   procedure Pre_Operation
     (Element :        Asis.Element;
      Control : in out Asis.Traverse_Control;
      State   : in out Traversal_State);
   --  Pre_Operation hook of the ASIS traversal of the syntax tree

   procedure Post_Operation
     (Element :        Asis.Element;
      Control : in out Asis.Traverse_Control;
      State   : in out Traversal_State);
   --  Post_Operation hook of the ASIS traversal of the syntax tree

   procedure Traverse_Source is new Asis.Iterator.Traverse_Element
     (State_Information => Traversal_State);

   procedure Record_Class (Element : Asis.Declaration);

   ----------------
   -- Load_Sinfo --
   ----------------

   procedure Load_Sinfo is
      Control : Traverse_Control := Continue;
      State   : Traversal_State := Before_Why_Node_Kind;
   begin
      --  Traversal of the syntax tree to gather kind/class names

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
   end Load_Sinfo;

   -------------------
   -- Pre_Operation --
   -------------------

   procedure Pre_Operation
     (Element :        Asis.Element;
      Control : in out Asis.Traverse_Control;
      State   : in out Traversal_State)
   is
      use String_Lists;

      pragma Unreferenced (Control);

      Kind : constant Flat_Element_Kinds := Flat_Element_Kind (Element);
   begin
      case State is
         when Before_Why_Node_Kind =>
            if Kind = A_Defining_Identifier then
               declare
                  Text : constant Asis.Program_Text := Img (Element);
               begin
                  if Text = "Why_Node_Kind" then
                     State := In_Why_Node_Kind;
                  end if;
               end;
            end if;

         when In_Why_Node_Kind =>
            if Kind = A_Defining_Enumeration_Literal then
               declare
                  Text : constant Asis.Program_Text := Img (Element);
               begin
                  Kinds.Append (new Wide_String'(Text));
               end;
            end if;

         when After_Why_Node_Kind =>
            if Kind = A_Subtype_Declaration then
               Record_Class (Element);
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

         when After_Why_Node_Kind =>
            null;
      end case;
   end Post_Operation;

   ------------------
   -- Record_Class --
   ------------------

   procedure Record_Class (Element : Asis.Declaration) is
      DI      : constant Asis.Defining_Name_List :=
                  Names (Element);
      Name    : constant Wide_String_Access :=
                  new Wide_String'(Img (DI (DI'First)));
      SI      : constant Asis.Subtype_Indication :=
                  Type_Declaration_View (Element);
      RC      : constant Asis.Constraint :=
                  Subtype_Constraint (SI);
      First_E : constant Asis.Element :=
                  Lower_Bound (RC);
      Last_E  : constant Asis.Element :=
                  Upper_Bound (RC);
      First   : constant Wide_String_Access :=
                  new Wide_String'(Img (First_E));
      Last    : constant Wide_String_Access :=
                  new Wide_String'(Img (Last_E));
      CI      : constant Class_Info :=
                  (Name  => Name,
                   First => First,
                   Last  => Last);
   begin
      pragma Assert (DI'Length = 1);
      Classes.Append (CI);
   end Record_Class;

end Xkind_Load;
