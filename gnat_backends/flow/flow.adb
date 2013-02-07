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
with Flow.Data_Dependence_Graph;
with Flow.Control_Dependence_Graph;

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

         function NDI (G : Flow_Graphs.T'Class;
                       N : Flow_Graphs.Vertex_Id)
                       return Flow_Graphs.Node_Display_Info;
         --  Pretty-printing for each node in the dot output. For now
         --  this is just the node number.

         function NDI (G : Flow_Graphs.T'Class;
                       N : Flow_Graphs.Vertex_Id)
                       return Flow_Graphs.Node_Display_Info
         is
            Rv : Flow_Graphs.Node_Display_Info :=
              Flow_Graphs.Node_Display_Info'
              (Show  => True,
               Shape => Flow_Graphs.Node_Shape_T'First,
               Label => Null_Unbounded_String);
         begin
            if N = FA.Start_Vertex then
               Rv.Label := To_Unbounded_String ("start");
            elsif N = FA.End_Vertex then
               Rv.Label := To_Unbounded_String ("end");
            else
               Temp_String := Null_Unbounded_String;
               Output.Set_Special_Output (Add_To_Temp_String'Access);
               declare
                  E : constant Entity_Id := G.Get_Key (N);
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
               Rv.Label := Temp_String;

               if G.Get_Attributes (N).Is_Null_Node then
                  Rv.Show := False;
               end if;
            end if;
            return Rv;
         end NDI;
      begin
         FA := Flow_Analysis_Graphs'
           (Start_Vertex => Flow_Graphs.Null_Vertex,
            End_Vertex   => Flow_Graphs.Null_Vertex,
            NTV          => Node_To_Vertex_Maps.Empty_Map,
            CFG          => Flow_Graphs.Create,
            DDG          => Flow_Graphs.Create,
            CDG          => Flow_Graphs.Create);

         Control_Flow_Graph.Create (Body_N, FA);

         FA.CFG.Write_Dot_File
           (Filename  => Get_Name_String (Chars (E)) & "_cfg",
            Node_Info => NDI'Access);

         Data_Dependence_Graph.Create (FA);

         FA.DDG.Write_Dot_File
           (Filename  => Get_Name_String (Chars (E)) & "_ddg",
            Node_Info => NDI'Access);

         Control_Dependence_Graph.Create (FA);

         FA.CDG.Write_Dot_File
           (Filename  => Get_Name_String (Chars (E)) & "_cdg",
            Node_Info => NDI'Access);

      end;
   end Flow_Analyse_Entity;

end Flow;
