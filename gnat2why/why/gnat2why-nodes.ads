------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                       G N A T 2 W H Y . N O D E S                        --
--                                                                          --
--                                  S p e c                                 --
--                                                                          --
--                        Copyright (C) 2012-2013, AdaCore                  --
--                                                                          --
-- gnat2why is  free  software;  you can redistribute  it and/or  modify it --
-- under terms of the  GNU General Public License as published  by the Free --
-- Software  Foundation;  either version 3,  or (at your option)  any later --
-- version.  gnat2why is distributed  in the hope that  it will be  useful, --
-- but WITHOUT ANY WARRANTY; without even the implied warranty of  MERCHAN- --
-- TABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public --
-- License for  more details.  You should have  received  a copy of the GNU --
-- General  Public License  distributed with  gnat2why;  see file COPYING3. --
-- If not,  go to  http://www.gnu.org/licenses  for a complete  copy of the --
-- license.                                                                 --
--                                                                          --
-- gnat2why is maintained by AdaCore (http://www.adacore.com)               --
--                                                                          --
------------------------------------------------------------------------------

with Ada.Containers;
with Ada.Containers.Doubly_Linked_Lists;
with Ada.Containers.Hashed_Sets;
with Ada.Containers.Hashed_Maps;

with SPARK_Frame_Conditions; use SPARK_Frame_Conditions;

with AA_Util;                use AA_Util;
with Atree;                  use Atree;
with Einfo;                  use Einfo;
with Namet;                  use Namet;
with Sinfo;                  use Sinfo;
with Sinput;                 use Sinput;
with Stand;                  use Stand;
with Types;                  use Types;

with Why.Ids;                use Why.Ids;
with Why.Types;              use Why.Types;

package Gnat2Why.Nodes is
   --  This package contains data structures and facilities to deal with the
   --  GNAT tree.

   package List_Of_Nodes is new Ada.Containers.Doubly_Linked_Lists (Node_Id);
   --  Standard list of nodes. It is often more convenient to use these,
   --  compared to List_Id in the GNAT frontend as a Node_Id can be in
   --  any number of these lists, while it can be only in one List_Id.

   function Node_Hash (X : Node_Id) return Ada.Containers.Hash_Type
   is (Ada.Containers.Hash_Type (X));
   --  Compute the hash of a node

   package Node_Sets is new Ada.Containers.Hashed_Sets
     (Element_Type        => Node_Id,
      Hash                => Node_Hash,
      Equivalent_Elements => "=",
      "="                 => "=");
   --  Sets of nodes

   package Node_Maps is new Ada.Containers.Hashed_Maps
     (Key_Type        => Node_Id,
      Element_Type    => Node_Id,
      Hash            => Node_Hash,
      Equivalent_Keys => "=",
      "="             => "=");
   --  Maps of nodes

   package Node_Graphs is new Ada.Containers.Hashed_Maps
     (Key_Type        => Node_Id,
      Element_Type    => Node_Sets.Set,
      Hash            => Node_Hash,
      Equivalent_Keys => "=",
      "="             => Node_Sets."=");
   --  Maps of nodes to sets of nodes

   procedure Add_To_Graph (Map : in out Node_Graphs.Map; From, To : Node_Id);
   --  Add the relation From -> To in the given graph

   function Get_Graph_Closure
     (Map  : Node_Graphs.Map;
      From : Node_Id) return Node_Sets.Set;
   --  Return the set of nodes reachable from node From by following the edges
   --  in the graph Map.

   package Ada_To_Why is new Ada.Containers.Hashed_Maps
     (Key_Type        => Node_Id,
      Element_Type    => Why_Node_Id,
      Hash            => Node_Hash,
      Equivalent_Keys => "=",
      "="             => "=");

   package Ada_Ent_To_Why is

      --  This package is a map from Ada names to Why nodes. Ada names can have
      --  the form of Entity_Ids or Entity_Names.

      type Map is private;
      type Cursor is private;

      Empty_Map : constant Map;

      procedure Insert (M : in out Map;
                        E : Entity_Id;
                        W : Why_Node_Id);

      procedure Insert (M : in out Map;
                        E : String;
                        W : Why_Node_Id);

      function Element (M : Map; E : Entity_Id) return Why_Node_Id;
      function Element (C : Cursor) return Why_Node_Id;

      function Find (M : Map; E : Entity_Id) return Cursor;
      function Find (M : Map; E : String) return Cursor;

      function Has_Element (M : Map; E : Entity_Id) return Boolean;
      function Has_Element (C : Cursor) return Boolean;

   private

      package Name_To_Why_Map is new Ada.Containers.Hashed_Maps
        (Key_Type => Entity_Name,
         Element_Type    => Why_Node_Id,
         Hash            => Name_Hash,
         Equivalent_Keys => Name_Equal,
         "="             => "=");

      type Map is record
         Entity_Ids   : Ada_To_Why.Map;
         Entity_Names : Name_To_Why_Map.Map;
      end record;

      Empty_Map : constant Map :=
        Map'(Entity_Ids    => Ada_To_Why.Empty_Map,
             Entity_Names => Name_To_Why_Map.Empty_Map);

      type Cursor_Kind is (CK_Ent, CK_Str);

      type Cursor is record

         --  This should be a variant record, but then it could not be a
         --  completion of the private type above, so here we have the
         --  invariant that when Kind = CK_Ent, then Ent_Cursor is valid,
         --  otherwise, Name_Cursor is valid.

         Kind        : Cursor_Kind;
         Ent_Cursor  : Ada_To_Why.Cursor;
         Name_Cursor : Name_To_Why_Map.Cursor;
      end record;

   end Ada_Ent_To_Why;

   function Has_Precondition (E : Entity_Id) return Boolean
   with Pre => Is_Overloadable (E);
   --  Check whether E (which must be the entity for a subprogram) has a
   --  precondition.

   function In_Main_Unit_Body (N : Node_Id) return Boolean;
   function In_Main_Unit_Spec (N : Node_Id) return Boolean;
   --  Check whether N is in the Body, respectively in the Spec of the current
   --  Unit

   function In_Some_Unit_Body (N : Node_Id) return Boolean;
   --  Return whether N is in a body

   function Is_In_Current_Unit (N : Node_Id) return Boolean;
   --  Return True when the node belongs to the Spec or Body of the current
   --  unit.

   function Is_In_Standard_Package (N : Node_Id) return Boolean is
     (Sloc (N) = Standard_Location or else
        Sloc (N) = Standard_ASCII_Location);
   --  Return true if the given node is defined in the standard package

   function In_Standard_Scope (Id : Entity_Id) return Boolean is
      (Scope (Id) = Standard_Standard
        or else Scope (Id) = Standard_ASCII);

   function Is_Package_Level_Entity (E : Entity_Id) return Boolean is
     (Ekind (Scope (E)) = E_Package);

   function Is_Quantified_Loop_Param (E : Entity_Id) return Boolean
   with Pre => (Ekind (E) = E_Loop_Parameter);
   --  check whether the E_Loop_Parameter in argument comes from a quantifier
   --  or not

   function Is_Pragma_Assert_And_Cut (N : Node_Id) return Boolean
   with Pre => (Nkind (N) = N_Pragma);

   function Translate_Location (Loc : Source_Ptr) return Source_Ptr is
     (if Instantiation_Location (Loc) /= No_Location then
        Instantiation_Location (Loc)
      else
        Loc);

   function File_Name (Loc : Source_Ptr) return String is
     (Get_Name_String (File_Name
                       (Get_Source_File_Index (Loc))));

   --  This function returns the file name of the source pointer (will return
   --  the file of the generic in case of instances)

   function File_Name_Without_Suffix (Loc : Source_Ptr) return String is
     (File_Name_Without_Suffix (File_Name (Translate_Location (Loc))));

   --  This function will return the file name of the source pointer of the
   --  suffix. Contrary to the File_Name function, this one returns the file
   --  name of the instance.

   function Source_Name (E : Entity_Id) return String;

   function Type_Of_Node (N : Node_Id) return String;
   --  Get the name of the type of an Ada node, as a string

   function Type_Of_Node (N : Node_Id) return Entity_Id;
   --  Get the name of the type of an Ada node, as a Node_Id of Kind
   --  N_Defining_Identifier

   function Type_Of_Node (N : Node_Id) return W_Base_Type_Id;
   --  Get the name of the type of an Ada node, as a Why Type

   function Get_Range (N : Node_Id) return Node_Id
      with Post =>
         (Present (Low_Bound (Get_Range'Result)) and then
          Present (High_Bound (Get_Range'Result)));
   --  Get the range of a range constraint or subtype definition.
   --  The return node is of kind N_Range

   function String_Of_Node (N : Node_Id) return String;
   --  Return the node as pretty printed Ada code, limited to 50 chars

   function Short_Name (E : Entity_Id) return String;
   --  Return the "short name" of an Ada entity, which corresponds to the
   --  actual name used for that entity in Why3 (as opposed to the name of
   --  the module)

   function Avoid_Why3_Keyword (S : String) return String;
   --  Append a "__" whenever S is equal to a Why3 keyword.
   --  also, lowercase the argument.

   function Subprogram_Full_Source_Name (E : Entity_Id) return String;
   --  For a subprogram entity, return its scoped name, e.g. for subprogram
   --  Nested in
   --
   --    package body P is
   --       procedure Lib_Level is
   --          procedure Nested is
   --     ....
   --  return P.Lib_Level.Nested. Casing of names is taken as it appears in the
   --  source.

end Gnat2Why.Nodes;
