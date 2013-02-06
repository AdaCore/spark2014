------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                                 F L O W                                  --
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

with Atree; use Atree;
with Einfo; use Einfo;
with Sinfo; use Sinfo;
with Namet; use Namet;

with Alfa.Definition; use Alfa.Definition;
with Alfa.Util;

with Flow.Control_Flow_Graph;

package body Flow is

   use type Flow_Graphs.Vertex_Id;

   -------------------------
   -- Flow_Analyse_Entity --
   -------------------------

   procedure Flow_Analyse_Entity (E : Entity_Id) is
   begin
      if not (Ekind (E) in Subprogram_Kind and then Body_In_Alfa (E)) then
         return;
      end if;

      declare
         Body_N : constant Node_Id := Alfa.Util.Get_Subprogram_Body (E);
         FA     : Flow_Analysis_Graphs;

         function PP (N : Flow_Graphs.Vertex_Id) return String;
         --  Pretty-printing for each node in the dot output. For now
         --  this is just the node number.

         function PP (N : Flow_Graphs.Vertex_Id) return String
         is
         begin
            if N = FA.Start_Vertex then
               return "start";
            elsif N = FA.End_Vertex then
               return "end";
            else
               return "other node";
            end if;
         end PP;
      begin
         Control_Flow_Graph.Create (Body_N, FA);

         FA.CFG.Write_Dot_File
           (Filename            => Get_Name_String (Chars (E)) & "_cfg",
            Show_Solitary_Nodes => True,
            PP                  => PP'Access);
      end;
   end Flow_Analyse_Entity;

end Flow;
