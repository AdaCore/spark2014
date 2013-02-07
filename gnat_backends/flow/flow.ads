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

with Ada.Containers.Hashed_Sets;
with Ada.Containers.Hashed_Maps;

with Types; use Types;

with Graph;

with Gnat2Why.Nodes; use Gnat2Why.Nodes;  -- Node_Sets and Node_Hash

package Flow is

   type V_Attributes is record
      Variables_Defined : Node_Sets.Set;
      Variables_Used    : Node_Sets.Set;
   end record;

   Null_Attributes : constant V_Attributes :=
     V_Attributes'(Variables_Defined => Node_Sets.Empty_Set,
                   Variables_Used    => Node_Sets.Empty_Set);

   package Flow_Graphs is new Graph
     (Vertex_Key        => Node_Id,
      Vertex_Attributes => V_Attributes,
      Null_Key          => Empty,
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
      NTV          : Node_To_Vertex_Maps.Map;
      CFG          : Flow_Graphs.T;
      DDG          : Flow_Graphs.T;
   end record;

   procedure Flow_Analyse_Entity (E : Entity_Id);
   --  Flow analyse the given entity. This subprogram does nothing for
   --  entities without a body and not in SPARK 2014.

end Flow;
