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

with Sinfo;  use Sinfo;
with Namet;  use Namet;
with Sprint; use Sprint;
with Debug;  use Debug;

with Output;

with Why;
with Alfa.Definition; use Alfa.Definition;
with Alfa.Util;

with Flow.Control_Flow_Graph;
with Flow.Data_Dependence_Graph;
with Flow.Control_Dependence_Graph;
with Flow.Program_Dependence_Graph;
with Flow.Analysis;

use type Ada.Containers.Count_Type;

package body Flow is

   use type Flow_Graphs.Vertex_Id;

   Temp_String : Unbounded_String := Null_Unbounded_String;

   Whitespace : constant Ada.Strings.Maps.Character_Set :=
     Ada.Strings.Maps.To_Set
       (" " & Ada.Characters.Latin_1.CR & Ada.Characters.Latin_1.LF);

   procedure Add_To_Temp_String (S : String);
   --  Nasty nasty hack to add the given string to a global variable,
   --  Temp_String. We use this to pretty print nodes via Sprint_Node.

   -------------------------
   -- Add_To_Temp_String  --
   -------------------------

   procedure Add_To_Temp_String (S : String) is
   begin
      Append
        (Temp_String,
         Trim (To_Unbounded_String (S), Whitespace, Whitespace));
   end Add_To_Temp_String;

   -----------------------
   -- Flow_Id operators --
   -----------------------

   function "=" (Left, Right : Flow_Id) return Boolean is
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

   function Hash (N : Flow_Id) return Ada.Containers.Hash_Type is
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

   --------------------
   -- Sprint_Flow_Id --
   --------------------

   procedure Sprint_Flow_Id (F : Flow_Id) is
   begin
      case F.Kind is
         when Null_Value =>
            Output.Write_Str ("<null>");
         when Direct_Mapping =>
            Sprint_Node (F.Node_A);
         when Record_Field =>
            raise Why.Not_Implemented;
         when Magic_String =>
            raise Why.Not_Implemented;
      end case;
   end Sprint_Flow_Id;

   ---------------------------
   -- Get_Direct_Mapping_Id --
   ---------------------------

   function Get_Direct_Mapping_Id (F : Flow_Id) return Node_Id is
   begin
      return F.Node_A;
   end Get_Direct_Mapping_Id;

   -------------------------------
   -- Loop_Parameter_From_Loop  --
   -------------------------------

   function Loop_Parameter_From_Loop (E : Entity_Id) return Entity_Id is
      N : Node_Id;
   begin
      N := Parent (E);
      pragma Assert (Nkind (N) = N_Implicit_Label_Declaration);

      N := Label_Construct (N);
      pragma Assert (Nkind (N) = N_Loop_Statement);

      N := Iteration_Scheme (N);
      if N = Empty then
         return Empty;
      end if;
      pragma Assert (Nkind (N) = N_Iteration_Scheme);

      N := Loop_Parameter_Specification (N);
      if N = Empty then
         return Empty;
      end if;
      pragma Assert (Nkind (N) = N_Loop_Parameter_Specification);

      return Defining_Identifier (N);
   end Loop_Parameter_From_Loop;

   -------------------------
   -- Flow_Analyse_Entity --
   -------------------------

   procedure Flow_Analyse_Entity (E : Entity_Id) is
      use Flow_Graphs;
   begin
      if not (Ekind (E) in Subprogram_Kind and then Body_In_Alfa (E)) then
         return;
      end if;

      declare
         Body_N : constant Node_Id := Alfa.Util.Get_Subprogram_Body (E);
         FA     : Flow_Analysis_Graphs;

         function NDI
           (G : T'Class;
            V : Vertex_Id) return Node_Display_Info;
         --  Pretty-printing for each vertex in the dot output.

         function EDI
           (G      : T'Class;
            A      : Vertex_Id;
            B      : Vertex_Id;
            Marked : Boolean;
            Colour : Edge_Colours) return Edge_Display_Info;
         --  Pretty-printing for each edge in the dot output.

         ---------
         -- NDI --
         ---------

         function NDI
           (G : T'Class;
            V : Vertex_Id) return Node_Display_Info
         is
            Rv : Node_Display_Info := Node_Display_Info'
              (Show   => True,
               Shape  => Flow_Graphs.Node_Shape_T'First,
               Colour => Null_Unbounded_String,
               Label  => Null_Unbounded_String);
         begin
            if G.Get_Attributes (V).Is_Null_Node then
               Rv.Show := False;
            elsif V = FA.Start_Vertex then
               Rv.Label := To_Unbounded_String ("start");
               Rv.Shape := Shape_None;
            elsif V = FA.End_Vertex then
               Rv.Label := To_Unbounded_String ("end");
               Rv.Shape := Shape_None;
            else
               Temp_String := Null_Unbounded_String;
               Output.Set_Special_Output (Add_To_Temp_String'Access);

               declare
                  F : constant Flow_Id      := G.Get_Key (V);
                  A : constant V_Attributes := G.Get_Attributes (V);
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
                              when N_Loop_Statement =>
                                 Rv.Shape := Shape_Diamond;
                                 if Iteration_Scheme (N) = Empty then
                                    --  Basic loop. Should never
                                    --  appear as a vertex in the
                                    --  graph.
                                    pragma Assert (False);
                                 elsif Condition (Iteration_Scheme (N)) /=
                                   Empty then
                                    --  While loop.
                                    Output.Write_Str ("while ");
                                    Sprint_Node
                                      (Condition (Iteration_Scheme (N)));
                                 else
                                    Sprint_Node
                                      (Iteration_Scheme (N));
                                 end if;

                              when N_Procedure_Call_Statement =>
                                 Rv.Shape := Shape_Box;
                                 Output.Write_Str ("call ");
                                 Sprint_Node (Name (N));

                              when others =>
                                 if A.Is_Parameter then
                                    Rv.Shape := Shape_None;

                                    case F.Variant is
                                       when In_View =>
                                          Sprint_Flow_Id (A.Parameter_Formal);
                                          Output.Write_Str ("'in");
                                          Output.Write_Str ("&nbsp;:=&nbsp;");
                                          Sprint_Flow_Id (A.Parameter_Actual);

                                       when Out_View =>
                                          Sprint_Flow_Id (A.Parameter_Actual);
                                          Output.Write_Str ("&nbsp;:=&nbsp;");
                                          Sprint_Flow_Id (A.Parameter_Formal);
                                          Output.Write_Str ("'out");
                                       when others =>
                                          raise Program_Error;
                                    end case;

                                 else
                                    Sprint_Node (N);
                                 end if;
                           end case;
                        end;

                        case F.Variant is
                           when Initial_Value =>
                              Rv.Shape := Shape_None;
                              Output.Write_Str ("'initial");

                              if not A.Is_Initialised then
                                 Rv.Colour := To_Unbounded_String ("red");
                              end if;

                           when Final_Value =>
                              Rv.Shape := Shape_None;
                              Output.Write_Str ("'final");
                              if A.Is_Export then
                                 Rv.Colour := To_Unbounded_String ("blue");
                              end if;

                           when others =>
                              null;
                        end case;
                     when others =>
                        raise Program_Error;
                  end case;

                  if A.Loops.Length > 0 and not A.Is_Parameter then
                     Output.Write_Str ("\nLoops:");
                     for Loop_Identifier of A.Loops loop
                        Output.Write_Str ("&nbsp;");
                        Sprint_Node (Loop_Identifier);
                     end loop;
                  end if;
               end;

               Output.Write_Eol;
               Output.Cancel_Special_Output;
               Rv.Label := Temp_String;
            end if;

            return Rv;
         end NDI;

         ---------
         -- EDI --
         ---------

         function EDI
           (G      : T'Class;
            A      : Vertex_Id;
            B      : Vertex_Id;
            Marked : Boolean;
            Colour : Edge_Colours) return Edge_Display_Info
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
           (Subprogram   => E,
            Start_Vertex => Flow_Graphs.Null_Vertex,
            End_Vertex   => Flow_Graphs.Null_Vertex,
            CFG          => Flow_Graphs.Create,
            DDG          => Flow_Graphs.Create,
            CDG          => Flow_Graphs.Create,
            PDG          => Flow_Graphs.Create,
            Vars         => Flow_Id_Sets.Empty_Set,
            Loops        => Node_Sets.Empty_Set);

         Control_Flow_Graph.Create (Body_N, FA);

         --  We print this graph first in cast the other algorithms
         --  barf.
         if Debug_Flag_Dot_ZZ then
            FA.CFG.Write_Pdf_File
              (Filename  => Get_Name_String (Chars (E)) & "_cfg",
               Node_Info => NDI'Access,
               Edge_Info => EDI'Access);
         end if;

         Data_Dependence_Graph.Create (FA);
         Control_Dependence_Graph.Create (FA);
         Program_Dependence_Graph.Create (FA);

         --  Now we print everything else.
         if Debug_Flag_Dot_ZZ then
            FA.DDG.Write_Pdf_File
              (Filename  => Get_Name_String (Chars (E)) & "_ddg",
               Node_Info => NDI'Access,
               Edge_Info => EDI'Access);

            FA.CDG.Write_Pdf_File
              (Filename  => Get_Name_String (Chars (E)) & "_cdg",
               Node_Info => NDI'Access,
               Edge_Info => EDI'Access);

            FA.PDG.Write_Pdf_File
              (Filename  => Get_Name_String (Chars (E)) & "_pdg",
               Node_Info => NDI'Access,
               Edge_Info => EDI'Access);
         end if;

         Analysis.Find_Ineffective_Imports (FA);
         Analysis.Find_Ineffective_Statements (FA);
         Analysis.Find_Use_Of_Uninitialised_Variables (FA);
         Analysis.Find_Stable_Elements (FA);

      end;
   end Flow_Analyse_Entity;

end Flow;
