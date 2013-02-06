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

with Ada.Strings.Unbounded; use Ada.Strings.Unbounded;
with Ada.Strings.Maps;
with Ada.Characters.Latin_1;

with Atree; use Atree;
with Einfo; use Einfo;
with Sinfo; use Sinfo;
with Namet; use Namet;
with Sprint; use Sprint;

with Output;

with Alfa.Definition; use Alfa.Definition;
with Alfa.Util;

with Flow.Control_Flow_Graph;

package body Flow is

   use type Flow_Graphs.Vertex_Id;

   Temp_String : Unbounded_String := Null_Unbounded_String;

   Whitespace : constant Ada.Strings.Maps.Character_Set :=
     Ada.Strings.Maps.To_Set (" " &
                                Ada.Characters.Latin_1.CR &
                                Ada.Characters.Latin_1.LF);

   procedure Add_To_Temp_String (S : String);
   --  Nasty nasty hack to add the given string to a global variable,
   --  Temp_String. We use this to pretty print nodes via Sprint_Node.

   -------------------------
   -- Add_To_Temp_String  --
   -------------------------

   procedure Add_To_Temp_String (S : String)
   is
   begin
      Append (Temp_String, Trim (To_Unbounded_String (S),
                                 Whitespace,
                                 Whitespace));
   end Add_To_Temp_String;

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
               Temp_String := Null_Unbounded_String;
               Output.Set_Special_Output (Add_To_Temp_String'Access);
               declare
                  E : constant Entity_Id := FA.CFG.Get_Key (N);
               begin
                  case Nkind (E) is
                     when N_If_Statement =>
                        Output.Write_Str ("if ");
                        Sprint_Node (Condition (E));
                     when others =>
                        Sprint_Node (E);
                  end case;
               end;
               Output.Write_Eol;
               Output.Cancel_Special_Output;
               return To_String (Temp_String);
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
