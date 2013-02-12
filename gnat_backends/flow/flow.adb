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

with Why;
with Alfa.Definition; use Alfa.Definition;
with Alfa.Util;

with Flow.Control_Flow_Graph;
with Flow.Data_Dependence_Graph;
with Flow.Control_Dependence_Graph;
with Flow.Program_Dependence_Graph;

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

   -----------------------
   -- Flow_Id operators --
   -----------------------

   function "=" (Left, Right : Flow_Id) return Boolean
   is
   begin
      if Left.Kind = Right.Kind then
         if Left.Variant = Right.Variant then
            case Left.Kind is
               when Null_Value =>
                  return True;
               when Direct_Mapping =>
                  return Left.Node_A = Right.Node_A;
               when Record_Field =>
                  raise Why.Not_Implemented;
               when Magic_String =>
                  return Name_Equal (Left.E_Name, Right.E_Name);
            end case;
         elsif Left.Kind = Null_Value then
            return True;
         else
            return False;
         end if;
      elsif Left.Kind = Direct_Mapping and Right.Kind = Magic_String then
         raise Why.Not_Implemented;
      elsif Left.Kind = Magic_String and Right.Kind = Direct_Mapping then
         raise Why.Not_Implemented;
      else
         return False;
      end if;
   end "=";

   ----------
   -- Hash --
   ----------

   function Hash (N : Flow_Id) return Ada.Containers.Hash_Type
   is
   begin
      case N.Kind is
         when Null_Value =>
            return 0;
         when Direct_Mapping =>
            return Ada.Containers.Hash_Type (N.Node_A);
         when Record_Field =>
            raise Why.Not_Implemented;
         when Magic_String =>
            return Name_Hash (N.E_Name);
      end case;
   end Hash;

   ---------------------------
   -- Get_Direct_Mapping_Id --
   ---------------------------

   function Get_Direct_Mapping_Id (F : Flow_Id) return Node_Id
   is
   begin
      return F.Node_A;
   end Get_Direct_Mapping_Id;

   -------------------------
   -- Flow_Analyse_Entity --
   -------------------------

   procedure Flow_Analyse_Entity (E : Entity_Id)
   is
      use Flow_Graphs;
   begin
      if not (Ekind (E) in Subprogram_Kind and then Body_In_Alfa (E)) then
         return;
      end if;

      declare
         Body_N : constant Node_Id := Alfa.Util.Get_Subprogram_Body (E);
         FA     : Flow_Analysis_Graphs;

         function NDI (G : T'Class;
                       V : Vertex_Id)
                       return Node_Display_Info;
         --  Pretty-printing for each vertex in the dot output.

         function EDI (G      : T'Class;
                       A      : Vertex_Id;
                       B      : Vertex_Id;
                       Marked : Boolean;
                       Colour : Edge_Colours)
                       return Edge_Display_Info;
         --  Pretty-printing for each edge in the dot output.

         function NDI (G : T'Class;
                       V : Vertex_Id)
                       return Node_Display_Info
         is
            Rv : Node_Display_Info := Node_Display_Info'
              (Show  => True,
               Shape => Flow_Graphs.Node_Shape_T'First,
               Label => Null_Unbounded_String);
         begin
            if V = FA.Start_Vertex then
               Rv.Label := To_Unbounded_String ("start");
               Rv.Shape := Shape_None;
            elsif V = FA.End_Vertex then
               Rv.Label := To_Unbounded_String ("end");
               Rv.Shape := Shape_None;
            else
               Temp_String := Null_Unbounded_String;
               Output.Set_Special_Output (Add_To_Temp_String'Access);
               declare
                  F : constant Flow_Id := G.Get_Key (V);
               begin
                  case F.Kind is
                     when Direct_Mapping =>
                        declare
                           N : constant Node_Id := Get_Direct_Mapping_Id (F);
                        begin
                           case Nkind (N) is
                              when N_If_Statement =>
                                 Rv.Shape := Shape_Diamond;
                                 Output.Write_Str ("if ");
                                 Sprint_Node (Condition (N));
                              when others =>
                                 Sprint_Node (N);
                           end case;
                        end;
                        case F.Variant is
                           when Initial_Value =>
                              Rv.Shape := Shape_None;
                              Output.Write_Str ("'initial");
                           when Final_Value =>
                              Rv.Shape := Shape_None;
                              Output.Write_Str ("'final");
                           when others =>
                              null;
                        end case;
                     when others =>
                        raise Program_Error;
                  end case;
               end;
               Output.Write_Eol;
               Output.Cancel_Special_Output;
               Rv.Label := Temp_String;

               if G.Get_Attributes (V).Is_Null_Node then
                  Rv.Show := False;
               end if;
            end if;
            return Rv;
         end NDI;

         function EDI (G      : T'Class;
                       A      : Vertex_Id;
                       B      : Vertex_Id;
                       Marked : Boolean;
                       Colour : Edge_Colours)
                       return Edge_Display_Info
         is
            pragma Unreferenced (G, A, B, Marked);

            Rv : Edge_Display_Info :=
              Edge_Display_Info'(Show   => True,
                                 Shape  => Edge_Normal,
                                 Colour => Null_Unbounded_String,
                                 Label  => Null_Unbounded_String);
         begin
            case Colour is
               when EC_Default =>
                  null;
               when EC_DDG =>
                  Rv.Colour := To_Unbounded_String ("red");
            end case;
            return Rv;
         end EDI;

      begin
         FA := Flow_Analysis_Graphs'
           (Start_Vertex => Flow_Graphs.Null_Vertex,
            End_Vertex   => Flow_Graphs.Null_Vertex,
            CFG          => Flow_Graphs.Create,
            DDG          => Flow_Graphs.Create,
            CDG          => Flow_Graphs.Create,
            PDG          => Flow_Graphs.Create,
            Vars         => Flow_Id_Sets.Empty_Set);

         Control_Flow_Graph.Create (Body_N, FA);

         FA.CFG.Write_Pdf_File
           (Filename  => Get_Name_String (Chars (E)) & "_cfg",
            Node_Info => NDI'Access,
            Edge_Info => EDI'Access);

         Data_Dependence_Graph.Create (FA);

         FA.DDG.Write_Pdf_File
           (Filename  => Get_Name_String (Chars (E)) & "_ddg",
            Node_Info => NDI'Access,
            Edge_Info => EDI'Access);

         Control_Dependence_Graph.Create (FA);

         FA.CDG.Write_Pdf_File
           (Filename  => Get_Name_String (Chars (E)) & "_cdg",
            Node_Info => NDI'Access,
            Edge_Info => EDI'Access);

         Program_Dependence_Graph.Create (FA);

         FA.PDG.Write_Pdf_File
           (Filename  => Get_Name_String (Chars (E)) & "_pdg",
            Node_Info => NDI'Access,
            Edge_Info => EDI'Access);

      end;
   end Flow_Analyse_Entity;

end Flow;
