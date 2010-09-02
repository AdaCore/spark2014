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

with Ada.Containers.Doubly_Linked_Lists;

with Asis;                       use Asis;
with Asis.Implementation;        use Asis.Implementation;
with Asis.Ada_Environments;      use Asis.Ada_Environments;
with Asis.Compilation_Units;     use Asis.Compilation_Units;
with Asis.Iterator;              use Asis.Iterator;
with Asis.Elements;              use Asis.Elements;
with Asis.Extensions.Flat_Kinds; use Asis.Extensions.Flat_Kinds;

with Utils;                      use Utils;
with Outputs;                    use Outputs;
with Templates;                  use Templates;

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

   type Wide_String_Access is access Wide_String;

   package String_Lists is
     new Ada.Containers.Doubly_Linked_Lists (Wide_String_Access, "=");

   Kinds   : String_Lists.List;
   --  List of node kinds; extracted from the syntax tree of Why.Sinfo
   --  by the ASIS traversal.

   Classes : String_Lists.List;
   --  List of node classes; extracted from the syntax tree of Why.Sinfo
   --  by the ASIS traversal.

   type Id_Kind is (Opaque, Unchecked, Regular);
   --  Three sort of Ids, as documented in Why.Ids

   type Id_Multiplicity is (Id_One, Id_Lone, Id_Some, Id_Set);
   --  Four multiplicity for Id subtype that matches as follows:
   --  * Id_One  is "Id",    representing exactly one node;
   --  * Id_Lone is "OId",   representing either zero (empty) or one node;
   --  * Id_Some is "List",  representing at least one node;
   --  * Id_Set  is "OList", representing any number of nodes.

   function Multiplicity_Suffix
     (Multiplicity : Id_Multiplicity)
     return Wide_String;
   --  Return the string suffix that corresponds to the given multiplicity

   function Id_Subtype
     (Prefix       : Wide_String;
      Kind         : Id_Kind;
      Multiplicity : Id_Multiplicity)
     return Wide_String;
   --  Return the suffix for the given Kind and the given Multiplicity.
   --  e.g. Id_Suffix ("W_Type", Opaque, Lone) would return
   --  "W_Type_Opaque_OId".

   function Base_Id_Subtype
     (Prefix       : Wide_String;
      Kind         : Id_Kind;
      Multiplicity : Id_Multiplicity)
     return Wide_String;
   --  Same as Id_Subtype, but returning the base subtype: i.e. Why_Node_Id
   --  for Opaque Ids, Opaque Ids for Unchecked Ids, Unchecked Ids for
   --  Regular Ids.

   procedure Print_Regular_Subtypes (O : in out Output_Record);
   --  Expand the kind-specific subtype declarations of Why_Node_Id
   --  and Why_Node_List. To each subtypes a predicate is associated
   --  that assert that the corresponding element in the node table is
   --  the root of a valid Why syntax tree.
   --  Same thing for classes.

   procedure Print_Unchecked_Subtypes (O : in out Output_Record);
   --  Same as Print_Subtypes, except that the expanded subtype will only
   --  be checked for kind-validity. e.g. a W_Type_Id always point to an
   --  element of kind W_Type in the node table; and W_Type_List contains only
   --  elements of kind W_Type.

   procedure Print_Opaque_Subtypes (O : in out Output_Record);
   --  Same as Print_Subtypes, except that the expanded subtype declarations
   --  will have no subtype predicate; (e.g. W_Type_Opaque_Id and
   --  W_Type_Opaque_List for kind W_Type).

   procedure Print_Subtypes (O : in out Output_Record; Kind : Id_Kind);
   --  Same as the three Print_*_Subtypes method, Kind being the
   --  Id Kind of the subtypes to generate.

   -------------------------
   -- Multiplicity_Suffix --
   -------------------------

   function Multiplicity_Suffix
     (Multiplicity : Id_Multiplicity)
     return Wide_String is
   begin
      case Multiplicity is
         when Id_One =>
            return "_Id";
         when Id_Lone =>
            return "_OId";
         when Id_Some =>
            return "_List";
         when Id_Set =>
            return "_OList";
      end case;
   end Multiplicity_Suffix;

   ----------------
   -- Id_Subtype --
   ----------------

   function Id_Subtype
     (Prefix       : Wide_String;
      Kind         : Id_Kind;
      Multiplicity : Id_Multiplicity)
     return Wide_String
   is
      function Kind_Suffix return Wide_String;
      --  Return the kind-specific part of the suffix

      -----------------
      -- Kind_Suffix --
      -----------------

      function Kind_Suffix return Wide_String is
      begin
         case Kind is
            when Opaque =>
               return "_Opaque";
            when Unchecked =>
               return "_Unchecked";
            when Regular =>
               return "";
         end case;
      end Kind_Suffix;

   begin
      return Prefix & Kind_Suffix & Multiplicity_Suffix (Multiplicity);
   end Id_Subtype;

   ---------------------
   -- Base_Id_Subtype --
   ---------------------

   function Base_Id_Subtype
     (Prefix       : Wide_String;
      Kind         : Id_Kind;
      Multiplicity : Id_Multiplicity)
     return Wide_String
   is
   begin
      case Kind is
         when Opaque =>
            case Multiplicity is
               when Id_One | Id_Lone =>
                  return "Why_Node_Id";
               when Id_Some | Id_Set =>
                  return "Why_Node_List";
            end case;
         when Unchecked =>
            return Id_Subtype (Prefix, Opaque, Multiplicity);
          when Regular =>
            return Id_Subtype (Prefix, Unchecked, Multiplicity);
      end case;
   end Base_Id_Subtype;

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

         when In_Why_Node_Class_Declaration =>
            if Kind = A_Defining_Identifier then
               declare
                  Text : constant Asis.Program_Text := Img (Element);
               begin
                  Classes.Append (new Wide_String'(Text));
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

   --------------------
   -- Print_Subtypes --
   --------------------

   procedure Print_Subtypes (O : in out Output_Record; Kind : Id_Kind) is
      use String_Lists;

      procedure Process_One_Node_Kind (Position : Cursor);
      --  Same as Print_Subtypes, but only for the kind
      --  pointed by Position.

      procedure Process_One_Class_Kind (Position : Cursor);
      --  Same as Print_Subtypes, but only for the class
      --  pointed by Position.

      procedure Print_Subtypes (Prefix : Wide_String);
      --  Print subtypes for a given node kind whose prefix
      --  is passed as parameter.

      procedure Print_Subtypes (Prefix : Wide_String) is
      begin
         for Multiplicity in Id_Multiplicity'Range loop
            P (O, "subtype "
                & Id_Subtype (Prefix, Kind, Multiplicity)
                & " is");

            if Kind = Opaque then
               P (O, " ");
            else
               NL (O);
               P (O, "  ");
            end if;

            PL (O, Base_Id_Subtype (Prefix, Kind, Multiplicity) & ";");

            if Kind /= Opaque then
               PL (O, "--  ??? subtype predicate not generated yet");
            end if;

            if Multiplicity /= Id_Multiplicity'Last then
               NL (O);
            end if;
         end loop;
      end Print_Subtypes;

      ----------------------------
      -- Process_One_Class_Kind --
      ----------------------------

      procedure Process_One_Class_Kind (Position : Cursor) is
         S : constant Wide_String_Access := String_Lists.Element (Position);
      begin
         Print_Subtypes (S.all);

         if Position /= Classes.Last then
            NL (O);
         end if;
      end Process_One_Class_Kind;

      ---------------------------
      -- Process_One_Node_Kind --
      ---------------------------

      procedure Process_One_Node_Kind (Position : Cursor) is
         S : constant Wide_String_Access := String_Lists.Element (Position);
      begin
         Print_Subtypes (S.all);

         if Position /= Kinds.Last then
            NL (O);
         end if;
      end Process_One_Node_Kind;

   --  Start of processing for Print_Subtypes

   begin
      Kinds.Iterate (Process_One_Node_Kind'Access);
      NL (O);
      Classes.Iterate (Process_One_Class_Kind'Access);
   end Print_Subtypes;

   ----------------------------
   -- Print_Regular_Subtypes --
   ----------------------------

   procedure Print_Regular_Subtypes (O : in out Output_Record) is
   begin
      Print_Subtypes (O, Regular);
   end Print_Regular_Subtypes;

   ------------------------------
   -- Print_Unchecked_Subtypes --
   ------------------------------

   procedure Print_Unchecked_Subtypes (O : in out Output_Record) is
   begin
      Print_Subtypes (O, Unchecked);
   end Print_Unchecked_Subtypes;

   ---------------------------
   -- Print_Opaque_Subtypes --
   ---------------------------

   procedure Print_Opaque_Subtypes (O : in out Output_Record) is
   begin
      Print_Subtypes (O, Opaque);
   end Print_Opaque_Subtypes;

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

   --  Production of packages from the kind/class lists

   Add ("Declare_Node_Ids", Print_Regular_Subtypes'Access);
   Add ("Declare_Unchecked_Ids", Print_Unchecked_Subtypes'Access);
   Add ("Declare_Opaque_Ids", Print_Opaque_Subtypes'Access);

   Process ("why-ids.ads");
   Process ("why-unchecked_ids.ads");
   Process ("why-opaque_ids.ads");
end Xkinds;
