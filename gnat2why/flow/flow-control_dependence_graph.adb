------------------------------------------------------------------------------
--                                                                          --
--                           GNAT2WHY COMPONENTS                            --
--                                                                          --
--        F L O W . C O N T R O L _ D E P E N D E N C E _ G R A P H         --
--                                                                          --
--                                 B o d y                                  --
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

package body Flow.Control_Dependence_Graph is

   procedure Create (FA : in out Flow_Analysis_Graphs)
   is
      Reversed_CFG : Flow_Graphs.T;
   begin
      --  Reverse CFG and add an edge from end -> start.
      Reversed_CFG := FA.CFG.Invert;
      Reversed_CFG.Add_Edge (FA.End_Vertex, FA.Start_Vertex, EC_Default);

      --  The CDG is simply the post-dominance frontier.
      FA.CDG := Reversed_CFG.Dominance_Frontier (FA.End_Vertex);

      --  Fix call nodes. As they appear as a linear sequence in the
      --  CFG the call vertex and each parameter vertex will all be
      --  control dependent on the same node. For clarity, we want all
      --  parameter vertices to be control dependent on the call
      --  vertex.
      for V of FA.CDG.Get_Collection (Flow_Graphs.All_Vertices) loop
         declare
            A : constant V_Attributes := FA.CDG.Get_Attributes (V);
         begin
            if A.Is_Parameter or A.Is_Global_Parameter then
               pragma Assert (FA.CDG.In_Neighbour_Count (V) = 1);
               pragma Assert (FA.CDG.Out_Neighbour_Count (V) = 0);
               FA.CDG.Clear_Vertex (V);
               FA.CDG.Add_Edge (FA.CDG.Get_Vertex (A.Call_Vertex),
                                V,
                                EC_Default);
            end if;
         end;
      end loop;
   end Create;

end Flow.Control_Dependence_Graph;
