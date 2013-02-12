------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                                 F L O W                                  --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                  Copyright (C) 2013, Altran UK Limited                   --
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
------------------------------------------------------------------------------

with Ada.Containers;
with Ada.Containers.Hashed_Sets;
with Ada.Containers.Hashed_Maps;

with Types;                 use Types;

with Gnat2Why.Nodes;        use Gnat2Why.Nodes;
--  Node_Sets and Node_Hash

with Alfa.Frame_Conditions; use Alfa.Frame_Conditions;
--  Entity_Name

with Graph;

package Flow is

   type Edge_Colours is (EC_Default, EC_DDG);

   type Flow_Id_Kind is (Null_Value,
                         Direct_Mapping,
                         Record_Field,
                         Magic_String);
   type Flow_Id_Variant is (Normal_Use, Initial_Value, Final_Value);

   type Flow_Id is record
      Kind    : Flow_Id_Kind;
      Variant : Flow_Id_Variant;
      Node_A  : Node_Id;
      Node_B  : Node_Id;
      E_Name  : Entity_Name;
   end record;

   function "=" (Left, Right : Flow_Id) return Boolean;

   Null_Flow_Id : constant Flow_Id := Flow_Id'(Kind    => Null_Value,
                                               Variant => Normal_Use,
                                               Node_A  => Empty,
                                               Node_B  => Empty,
                                               E_Name  => Null_Entity_Name);

   function Hash (N : Flow_Id) return Ada.Containers.Hash_Type;

   function Direct_Mapping_Id (N       : Node_Id;
                               Variant : Flow_Id_Variant := Normal_Use)
                               return Flow_Id
   is (Flow_Id'(Kind    => Direct_Mapping,
                Variant => Variant,
                Node_A  => N,
                Node_B  => Empty,
                E_Name  => Null_Entity_Name));

   function Get_Direct_Mapping_Id
     (F : Flow_Id)
      return Node_Id
      with Pre => (F.Kind = Direct_Mapping);

   package Flow_Id_Sets is new Ada.Containers.Hashed_Sets
     (Element_Type        => Flow_Id,
      Hash                => Hash,
      Equivalent_Elements => "=",
      "="                 => "=");

   type V_Attributes is record
      Is_Null_Node      : Boolean;
      Variables_Defined : Flow_Id_Sets.Set;
      Variables_Used    : Flow_Id_Sets.Set;
   end record;

   Null_Attributes : constant V_Attributes :=
     V_Attributes'(Is_Null_Node      => False,
                   Variables_Defined => Flow_Id_Sets.Empty_Set,
                   Variables_Used    => Flow_Id_Sets.Empty_Set);

   Null_Node_Attributes : constant V_Attributes :=
     V_Attributes'(Is_Null_Node      => True,
                   Variables_Defined => Flow_Id_Sets.Empty_Set,
                   Variables_Used    => Flow_Id_Sets.Empty_Set);

   package Flow_Graphs is new Graph
     (Vertex_Key        => Flow_Id,
      Vertex_Attributes => V_Attributes,
      Edge_Colours      => Edge_Colours,
      Null_Key          => Null_Flow_Id,
      Test_Key          => "=");

   package Node_To_Vertex_Maps is new Ada.Containers.Hashed_Maps
     (Key_Type        => Node_Id,
      Element_Type    => Flow_Graphs.Vertex_Id,
      Hash            => Node_Hash,
      Equivalent_Keys => "=",
      "="             => Flow_Graphs."=");

   package Vertex_Sets is new Ada.Containers.Hashed_Sets
     (Element_Type        => Flow_Graphs.Vertex_Id,
      Hash                => Flow_Graphs.Vertex_Hash,
      Equivalent_Elements => Flow_Graphs."=",
      "="                 => Flow_Graphs."=");

   type Flow_Analysis_Graphs is record
      Start_Vertex : Flow_Graphs.Vertex_Id;
      End_Vertex   : Flow_Graphs.Vertex_Id;
      CFG          : Flow_Graphs.T;
      DDG          : Flow_Graphs.T;
      CDG          : Flow_Graphs.T;
      Vars         : Flow_Id_Sets.Set;
   end record;

   procedure Flow_Analyse_Entity (E : Entity_Id);
   --  Flow analyse the given entity. This subprogram does nothing for
   --  entities without a body and not in SPARK 2014.

end Flow;
