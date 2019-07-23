------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--        F L O W . P R O G R A M _ D E P E N D E N C E _ G R A P H         --
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

package body Flow.Program_Dependence_Graph is

   ------------
   -- Create --
   ------------

   procedure Create
     (FA : in out Flow_Analysis_Graphs) is
   begin
      --  Initialize the PDG with a copy of the vertices of the CFG,
      --  but not the edges
      FA.PDG := FA.CFG.Create;

      --  Edges in the PDG are the union of edges from the CDG, DDG and TDG
      FA.PDG.Copy_Edges (FA.CDG);
      FA.PDG.Copy_Edges (FA.DDG);
      FA.PDG.Copy_Edges (FA.TDG);
   end Create;

end Flow.Program_Dependence_Graph;
