------------------------------------------------------------------------------
--                                                                          --
--                           GNAT2WHY COMPONENTS                            --
--                                                                          --
--        F L O W . C O N T R O L _ D E P E N D E N C E _ G R A P H         --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                Copyright (C) 2013-2019, Altran UK Limited                --
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
      Reversed_CFG : Flow_Graphs.Graph;
   begin
      --  Reverse CFG and add an edge from end -> start
      Reversed_CFG := FA.CFG.Invert;
      Reversed_CFG.Add_Edge (FA.End_Vertex, FA.Start_Vertex, EC_Default);

      --  The CDG is simply the post-dominance frontier.
      FA.CDG := Reversed_CFG.Dominance_Frontier (FA.End_Vertex);

      --  Fix call nodes. As they appear as a linear sequence in the CFG the
      --  call vertex and each parameter vertex will all be control dependent
      --  on the same node. For clarity, we want all parameter vertices to be
      --  control dependent on the call vertex.
      --
      --  There are a few complications here, triggered by loops which are
      --  executed at least once (i.e. general loops and for loops over a
      --  statically non-empty range). We have quite involved sanity checks
      --  which push up the complexity (path finding is linear), but this
      --  kind of graph fiddeling is much easier to justify that way.

      for V of FA.CDG.Get_Collection (Flow_Graphs.All_Vertices) loop
         declare
            A  : V_Attributes renames FA.Atr (V);
         begin
            if A.Is_Parameter
              or else A.Is_Global_Parameter
              or else A.Is_Implicit_Parameter
            then
               declare
                  CV : constant Flow_Graphs.Vertex_Id :=
                    FA.CDG.Get_Vertex (A.Call_Vertex);

                  use type Flow_Graphs.Vertex_Id;
               begin
                  --  Sanity check that we will not lose control dependence
                  for P of FA.CDG.Get_Collection (V, Flow_Graphs.In_Neighbours)
                  loop
                     if P = V then
                        --  Self dependence is OK and we don't care if it
                        --  disappears.
                        null;

                     elsif FA.CDG.Non_Trivial_Path_Exists (P, CV) then
                        --  The call vertex is ultimately control dependent
                        --  on the in neighbour we are eliminating from our
                        --  parameter vertex, so we don't really lose anything.
                        null;

                     else
                        --  Bath, we have a problem
                        raise Program_Error;
                     end if;
                  end loop;

                  --  Sanity check that we won't lose outwards control
                  --  influence.
                  for S of FA.CDG.Get_Collection
                                    (V, Flow_Graphs.Out_Neighbours)
                  loop
                     if S = V then
                        --  Self dependence is OK and we don't care if it
                        --  disappears.
                        null;

                     elsif S = CV
                       or else CV = FA.CDG.Get_Vertex (FA.Atr (S).Call_Vertex)
                     then
                        --  This can happen if we have infinite loops
                        null;

                     else
                        --  Panic!
                        raise Program_Error;
                     end if;
                  end loop;

                  FA.CDG.Clear_Vertex (V);
                  FA.CDG.Add_Edge (CV, V, EC_Default);
               end;
            end if;
         end;
      end loop;
   end Create;

end Flow.Control_Dependence_Graph;
