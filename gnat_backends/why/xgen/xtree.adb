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

with Asis;                       use Asis;
with Asis.Implementation;        use Asis.Implementation;
with Asis.Declarations;          use Asis.Declarations;
with Asis.Definitions;           use Asis.Definitions;
with Asis.Ada_Environments;      use Asis.Ada_Environments;
with Asis.Compilation_Units;     use Asis.Compilation_Units;
with Asis.Iterator;              use Asis.Iterator;
with Asis.Elements;              use Asis.Elements;
with Asis.Extensions.Flat_Kinds; use Asis.Extensions.Flat_Kinds;

with Xtree_Tables;               use Xtree_Tables;
with Xtree_Builders;             use Xtree_Builders;
with Xtree_Accessors;            use Xtree_Accessors;
with Xtree_Traversal;            use Xtree_Traversal;
with Why.Sinfo;                  use Why.Sinfo;
with Utils;                      use Utils;
with Templates;                  use Templates;

procedure Xtree is
   --  ASIS helper that takes Why.Atree's syntax tree and generates
   --  builders, accessors/mutators, recursive traversal...

   My_Context : Asis.Context;

   type Traversal_Step is
     (Before_Why_Node,
      In_Why_Node,
      In_Variant,
      After_Why_Node);
   --  The traversal of the syntax tree is implemented as a state machine
   --  whose states are defined by this enumeration and whose transitions
   --  are triggered by the detection of some Ada entities. See the
   --  case statements in Pre_Operation/Post_Operation for more details
   --  about these states and transitions.

   type Traversal_State is record
      Step : Traversal_Step := Before_Why_Node;
   end record;

   procedure Pre_Operation
     (Element : Asis.Element;
      Control : in out Asis.Traverse_Control;
      State   : in out Traversal_State);
   --  Pre_Operation hook of the ASIS traversal of the syntax tree

   procedure Post_Operation
     (Element : Asis.Element;
      Control : in out Asis.Traverse_Control;
      State   : in out Traversal_State);
   --  Post_Operation hook of the ASIS traversal of the syntax tree

   procedure Traverse_Source is new Asis.Iterator.Traverse_Element
     (State_Information => Traversal_State);

   procedure Record_Field
     (NI         : in out Why_Node_Info;
      Element    : Asis.Component_Declaration;
      In_Variant : Boolean);
   --  Extract field informations from the component declaration
   --  and record it into Xtree_Tables.

   procedure Record_Variant (Element : Asis.Variant);
   --  Extract variant informations from the variant node in the syntax tree
   --  and record it into Xtree_Tables.

   -------------------
   -- Pre_Operation --
   -------------------

   procedure Pre_Operation
     (Element : Asis.Element;
      Control : in out Asis.Traverse_Control;
      State   : in out Traversal_State)
   is
      pragma Unreferenced (Control);

      Kind : constant Flat_Element_Kinds := Flat_Element_Kind (Element);
   begin
      case State.Step is
         when Before_Why_Node =>
            if Kind = A_Defining_Identifier then
               declare
                  Text : constant Asis.Program_Text := Img (Element);
               begin
                  if Text = "Why_Node" then
                     State.Step := In_Why_Node;
                  end if;
               end;
            end if;

         when In_Why_Node =>
            if Kind = A_Component_Declaration then
               Record_Field (Common_Fields, Element, False);

            elsif Kind = A_Variant then
               Record_Variant (Element);
               State.Step := In_Variant;
            end if;

         when In_Variant =>
            null;

         when After_Why_Node =>
            null;

      end case;
   end Pre_Operation;

   --------------------
   -- Post_Operation --
   --------------------

   procedure Post_Operation
     (Element : Asis.Element;
      Control : in out Asis.Traverse_Control;
      State   : in out Traversal_State)
   is
      pragma Unreferenced (Control);

      Kind : constant Flat_Element_Kinds := Flat_Element_Kind (Element);
   begin
      case State.Step is
         when Before_Why_Node =>
            null;

         when In_Why_Node =>
            if Kind = An_Enumeration_Type_Definition then
               State.Step := After_Why_Node;
            end if;

         when In_Variant =>
            if Kind = A_Variant then
               State.Step := In_Why_Node;
            end if;

         when After_Why_Node =>
            null;
      end case;
   end Post_Operation;

   ------------------
   -- Record_Field --
   ------------------

   procedure Record_Field
     (NI         : in out Why_Node_Info;
      Element    : Asis.Component_Declaration;
      In_Variant : Boolean)
   is
      C_Names    : constant Asis.Defining_Name_List :=
                     Names (Element);
      Name       : constant Defining_Name :=
                     C_Names (C_Names'First);
      Name_Image : constant Program_Text :=
                     Defining_Name_Image (Name);
      C_Def      : constant Asis.Component_Definition :=
                     Object_Declaration_View (Element);
      Type_Image : constant Program_Text := Img (C_Def);
   begin
      pragma Assert (C_Names'Length = 1);
      --  Support only one name only per component declaration
      New_Field (NI, In_Variant, Name_Image, Type_Image);
   end Record_Field;

   --------------------
   -- Record_Variant --
   --------------------

   procedure Record_Variant
     (Element : Asis.Variant)
   is
      V_Components : constant Asis.Record_Component_List :=
                          Record_Components (Element);
      Choices      : constant Asis.Element_List := Variant_Choices (Element);
      Choice       : constant Asis.Element := Choices (Choices'First);
      V_First      : Why_Node_Kind;
      V_Last       : Why_Node_Kind;
   begin
      pragma Assert (Choices'Length = 1);
      --  Support only one discrete choice in variant; either an
      --  Enumeration litteral, or a range.

      if Definition_Kind (Choice) = A_Discrete_Range then
         declare
            First_E : constant Asis.Expression := Lower_Bound (Choice);
            Last_E  : constant Asis.Expression := Upper_Bound (Choice);
            First_I : constant Wide_String := Img (First_E);
            Last_I  : constant Wide_String := Img (Last_E);
         begin
            V_First := Why_Node_Kind'Wide_Value (First_I);
            V_Last := Why_Node_Kind'Wide_Value (Last_I);
         end;
      else
         declare
            Choice_I : constant Wide_String := Img (Choice);
         begin
            V_First := Why_Node_Kind'Wide_Value (Choice_I);
            V_Last := Why_Node_Kind'Wide_Value (Choice_I);
         end;
      end if;

      for Kind in V_First .. V_Last loop
         Why_Tree_Info (Kind).Variant_Range_First := V_First;
         Why_Tree_Info (Kind).Variant_Range_Last := V_Last;

         for J in V_Components'First .. V_Components'Last loop
            if Flat_Element_Kind (V_Components (J)) /= A_Null_Component then
               Record_Field (Why_Tree_Info (Kind), V_Components (J), True);
            end if;
         end loop;
      end loop;
   end Record_Variant;

   Control : Traverse_Control := Continue;
   State   : Traversal_State;
begin
   --  Traversal of the syntax tree to gather structural infos of
   --  Why syntax trees

   Implementation.Initialize ("-ws");
   Ada_Environments.Associate
    (My_Context, "My Asis Context", "-C1 ./why-atree.adt");
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

   --  Production of packages for builders, accessors, mutators

   Add ("Declare_Builders", Print_Builder_Declarations'Access);
   Add ("Declare_Unchecked_Builders",
        Print_Unchecked_Builder_Declarations'Access);
   Add ("Implement_Builders", Print_Builder_Bodies'Access);
   Add ("Implement_Unchecked_Builders",
        Print_Unchecked_Builder_Bodies'Access);
   Add ("Declare_Accessors", Print_Accessor_Declarations'Access);
   Add ("Implement_Accessors", Print_Accessor_Bodies'Access);
   Add ("Declare_Traversal_Ops", Print_Traversal_Op_Declarations'Access);
   Add ("Implement_Traverse", Print_Traverse_Body'Access);
   Add ("Declare_Traversal_Op_Stubs",
        Print_Traversal_Op_Stub_Declarations'Access);
   Add ("Implement_Traversal_Op_Stubs",
        Print_Traversal_Op_Stub_Bodies'Access);

   Process ("why-atree-builders.ads");
   Process ("why-atree-builders.adb");
   Process ("why-atree-accessors.ads");
   Process ("why-atree-traversal.ads");
   Process ("why-atree-traversal.adb");
   Process ("why-atree-traversal_stub.ads");
   Process ("why-atree-traversal_stub.adb");
end Xtree;
