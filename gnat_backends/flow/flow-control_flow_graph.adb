------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--              F L O W . C O N T R O L _ F L O W _ G R A P H               --
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

with Treepr; use Treepr;

package body Flow.Control_Flow_Graph
is
   --  type Graph_Connections is record
   --     Standard_Entry : Flow_Graphs.Vertex_Id;
   --     Standard_Exits : Vertex_Sets.Set;
   --  end record;

   --  package Connection_Maps is new Ada.Containers.Hashed_Maps
   --    (Key_Type        => Node_Id,
   --     Element_Type    => Graph_Connections,
   --     Hash            => Node_Hash,
   --     Equivalent_Keys => "=",
   --     "="             => "=");

   procedure Create
     (E  : Entity_Id;
      FA : out Flow_Analysis_Graphs)
   is
      --  Connection_Map : Connection_Maps.Map;
   begin
      --  Start with a blank slate.
      FA := Flow_Analysis_Graphs'
        (Start_Vertex => Flow_Graphs.Null_Vertex,
         End_Vertex   => Flow_Graphs.Null_Vertex,
         NTV          => Node_To_Vertex_Maps.Empty_Map,
         CFG          => Flow_Graphs.Create);
      --  Connection_Map := Connection_Maps.Empty_Map;

      --  Print the node for debug purposes
      Print_Node_Subtree (E);

      --  Create the magic start and end vertices.
      FA.CFG.Add_Vertex (Null_Attributes, FA.Start_Vertex);
      FA.CFG.Add_Vertex (Null_Attributes, FA.End_Vertex);
   end Create;

end Flow.Control_Flow_Graph;
