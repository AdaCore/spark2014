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

with Aspects;  use Aspects;
with Debug;    use Debug;
with Namet;    use Namet;
with Nlists;   use Nlists;
with Sem_Util; use Sem_Util;
with Sinfo;    use Sinfo;
with Snames;   use Snames;
with Sprint;   use Sprint;

with Output;

with Why;
with Alfa.Definition; use Alfa.Definition;
with Alfa.Util;

with Flow.Control_Flow_Graph;
with Flow.Data_Dependence_Graph;
with Flow.Control_Dependence_Graph;
with Flow.Interprocedural;
with Flow.Program_Dependence_Graph;
with Flow.Analysis;

use type Ada.Containers.Count_Type;

package body Flow is

   Debug_Print_CFG           : constant Boolean := True;
   Debug_Print_Intermediates : constant Boolean := False;
   Debug_Print_PDG           : constant Boolean := True;

   use Flow_Graphs;

   Temp_String : Unbounded_String := Null_Unbounded_String;

   Whitespace : constant Ada.Strings.Maps.Character_Set :=
     Ada.Strings.Maps.To_Set
       (" " & Ada.Characters.Latin_1.CR & Ada.Characters.Latin_1.LF);

   procedure Add_To_Temp_String (S : String);
   --  Nasty nasty hack to add the given string to a global variable,
   --  Temp_String. We use this to pretty print nodes via Sprint_Node.

   function Flow_Analyse_Entity (E : Entity_Id) return Flow_Analysis_Graphs
     with Pre => (Ekind (E) in Subprogram_Kind and then Body_In_Alfa (E));
   --  Flow analyse the given entity. This subprogram does nothing for
   --  entities without a body and not in SPARK 2014.

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

   -------------------
   -- Print_Flow_Id --
   -------------------

   procedure Print_Flow_Id (F : Flow_Id) is
   begin
      Sprint_Flow_Id (F);
      case F.Variant is
         when Normal_Use =>
            null;
         when Initial_Value =>
            Output.Write_Str ("'initial");
         when Final_Value =>
            Output.Write_Str ("'initial");
         when In_View =>
            Output.Write_Str ("'in");
         when Out_View =>
            Output.Write_Str ("'out");
      end case;
      case F.Kind is
         when Null_Value =>
            null;
         when Direct_Mapping =>
            Output.Write_Str (" (direct)");
         when Record_Field =>
            Output.Write_Str (" (record)");
         when Magic_String =>
            Output.Write_Str (" (magic)");
      end case;
      Output.Write_Eol;
   end Print_Flow_Id;

   ---------------------------
   -- Get_Direct_Mapping_Id --
   ---------------------------

   function Get_Direct_Mapping_Id (F : Flow_Id) return Node_Id is
   begin
      return F.Node_A;
   end Get_Direct_Mapping_Id;

   --------------------
   -- Change_Variant --
   --------------------

   function Change_Variant (F       : Flow_Id;
                            Variant : Flow_Id_Variant)
                           return Flow_Id is
   begin
      case F.Kind is
         when Null_Value =>
            return Null_Flow_Id;
         when Direct_Mapping =>
            return Direct_Mapping_Id (Get_Direct_Mapping_Id (F), Variant);
         when others =>
            raise Why.Not_Implemented;
      end case;
   end Change_Variant;

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

   -----------------
   -- Get_Globals --
   -----------------

   procedure Get_Globals (Subprogram : Entity_Id;
                          Reads      : out Flow_Id_Sets.Set;
                          Writes     : out Flow_Id_Sets.Set)
   is
   begin
      Reads  := Flow_Id_Sets.Empty_Set;
      Writes := Flow_Id_Sets.Empty_Set;

      if Has_Aspect (Subprogram, Aspect_Global) then
         declare
            Global : constant Node_Id :=
              Aspect_Rep_Item (Find_Aspect (Subprogram, Aspect_Global));
            pragma Assert
              (List_Length (Pragma_Argument_Associations (Global)) = 1);

            PAA : constant Node_Id :=
              First (Pragma_Argument_Associations (Global));
            pragma Assert (Nkind (PAA) = N_Pragma_Argument_Association);

            CA       : List_Id;

            Row      : Node_Id;
            The_Mode : Name_Id;
            RHS      : Node_Id;

            procedure Process (The_Mode   : Name_Id;
                               The_Global : Entity_Id);
            --  Add the given global to the reads or writes list,
            --  depending on the mode.

            procedure Process (The_Mode   : Name_Id;
                               The_Global : Entity_Id)
            is
            begin
               case The_Mode is
                  when Name_Input =>
                     Reads.Insert (Direct_Mapping_Id
                                     (The_Global, In_View));
                  when Name_In_Out =>
                     Reads.Insert (Direct_Mapping_Id
                                     (The_Global, In_View));
                     Writes.Insert (Direct_Mapping_Id
                                      (The_Global, Out_View));
                  when Name_Output =>
                     Writes.Insert (Direct_Mapping_Id
                                      (The_Global, Out_View));
                  when others =>
                     raise Program_Error;
               end case;
            end Process;
         begin
            if Nkind (Expression (PAA)) = N_Null then
               --  No globals. We are good to return as is.
               return;
            else
               CA := Component_Associations (Expression (PAA));
            end if;

            Row := First (CA);
            while Row /= Empty loop
               pragma Assert (List_Length (Choices (Row)) = 1);
               The_Mode := Chars (First (Choices (Row)));

               RHS := Expression (Row);
               case Nkind (RHS) is
                  when N_Aggregate =>
                     RHS := First (Expressions (RHS));
                     while RHS /= Empty loop
                        Process (The_Mode, Entity (RHS));
                        RHS := Next (RHS);
                     end loop;
                  when N_Identifier =>
                     Process (The_Mode, Entity (RHS));
                  when N_Null =>
                     null;
                  when others =>
                     raise Why.Not_Implemented;
               end case;

               Row := Next (Row);
            end loop;
         end;

      else
         --  We don't have a global aspect, so we should look at the
         --  computed globals...

         declare
            ALI_Reads  : constant Name_Set.Set := Get_Reads (Subprogram);
            ALI_Writes : constant Name_Set.Set := Get_Writes (Subprogram);

            function Get_Flow_Id (Name : String;
                                  View : Parameter_Variant)
                                  return Flow_Id;
            --  Return a suitable flow id for the unique_name of an
            --  entity. We try our best to get a direct mapping,
            --  resorting to the magic string only as a last resort.

            function Get_Flow_Id (Name : String;
                                  View : Parameter_Variant)
                                  return Flow_Id
            is
            begin
               for E of All_Entities loop
                  if Unique_Name (E) = Name then
                     return Direct_Mapping_Id (E, View);
                  end if;
               end loop;
               raise Why.Not_Implemented;
            end Get_Flow_Id;

         begin
            for R of ALI_Reads loop
               Reads.Include (Get_Flow_Id (R.all, In_View));
            end loop;
            for W of ALI_Writes loop
               --  This is not a mistake, we must assume that all
               --  values written may also not change or that they are
               --  only partially updated.
               Reads.Include (Get_Flow_Id (W.all, In_View));
               Writes.Include (Get_Flow_Id (W.all, Out_View));
            end loop;
         end;

      end if;

   end Get_Globals;

   -----------------
   -- Print_Graph --
   -----------------

   procedure Print_Graph
     (Filename     : String;
      G            : T;
      Start_Vertex : Vertex_Id := Null_Vertex;
      End_Vertex   : Vertex_Id := Null_Vertex) is

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
            Shape  => Node_Shape_T'First,
            Colour => Null_Unbounded_String,
            Label  => Null_Unbounded_String);

         F : constant Flow_Id      := G.Get_Key (V);
         A : constant V_Attributes := G.Get_Attributes (V);
      begin
         Temp_String := Null_Unbounded_String;
         Output.Set_Special_Output (Add_To_Temp_String'Access);

         if A.Is_Null_Node then
            Rv.Show := False;

         elsif V = Start_Vertex then
            Rv.Label := To_Unbounded_String ("start");
            Rv.Shape := Shape_None;
            Rv.Show  := G.In_Neighbour_Count (V) > 0 or
              G.Out_Neighbour_Count (V) > 0;

         elsif V = End_Vertex then
            Rv.Label := To_Unbounded_String ("end");
            Rv.Shape := Shape_None;
            Rv.Show  := G.In_Neighbour_Count (V) > 0 or
              G.Out_Neighbour_Count (V) > 0;

         elsif A.Is_Parameter then
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

         elsif A.Is_Global_Parameter then
            Rv.Shape := Shape_None;

            Output.Write_Str ("global&nbsp;");
            Sprint_Flow_Id (A.Parameter_Formal);
            case A.Parameter_Formal.Variant is
               when In_View =>
                  Output.Write_Str ("'in");

               when Out_View =>
                  Output.Write_Str ("'out");

               when others =>
                  raise Program_Error;
            end case;

         else
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
                           Sprint_Node (N);
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
                        elsif A.Is_Constant then
                           Rv.Colour := To_Unbounded_String ("red");
                        end if;

                     when others =>
                        null;
                  end case;

               when others =>
                  raise Why.Not_Implemented;
            end case;

            if A.Loops.Length > 0 and not (A.Is_Parameter or
                                             A.Is_Global_Parameter) then
               Output.Write_Str ("\nLoops:");
               for Loop_Identifier of A.Loops loop
                  Output.Write_Str ("&nbsp;");
                  Sprint_Node (Loop_Identifier);
               end loop;
            end if;

            if A.Perform_IPFA then
               Output.Write_Str ("\nIPFA");
            end if;

            if A.Is_Global then
               Output.Write_Str ("\n(global)");
            end if;
         end if;

         Output.Write_Eol;
         Output.Cancel_Special_Output;

         if Length (Temp_String) > 0 then
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
            when EC_TD =>
               Rv.Colour := To_Unbounded_String ("cornflowerblue");
         end case;
         return Rv;
      end EDI;
   begin
      G.Write_Pdf_File
        (Filename  => Filename,
         Node_Info => NDI'Access,
         Edge_Info => EDI'Access);
   end Print_Graph;

   -------------------------
   -- Flow_Analyse_Entity --
   -------------------------

   function Flow_Analyse_Entity (E : Entity_Id) return Flow_Analysis_Graphs is
      Body_N : constant Node_Id := Alfa.Util.Get_Subprogram_Body (E);
      FA     : Flow_Analysis_Graphs;
   begin
      FA := Flow_Analysis_Graphs'
        (Subprogram   => E,
         Start_Vertex => Null_Vertex,
         End_Vertex   => Null_Vertex,
         CFG          => Create,
         DDG          => Create,
         CDG          => Create,
         TDG          => Create,
         PDG          => Create,
         All_Vars     => Flow_Id_Sets.Empty_Set,
         Loops        => Node_Sets.Empty_Set);

      if Debug_Flag_Dot_ZZ then
         Output.Write_Str (Character'Val (8#33#) & "[32m" &
                             "Flow analysis (cons) of " &
                             Get_Name_String (Chars (E)) &
                             Character'Val (8#33#) & "[0m");
         Output.Write_Eol;
      end if;
      Control_Flow_Graph.Create (Body_N, FA);

      --  We print this graph first in cast the other algorithms
      --  barf.
      if Debug_Flag_Dot_ZZ and Debug_Print_CFG then
         Print_Graph (Filename     => Get_Name_String (Chars (E)) & "_cfg",
                      G            => FA.CFG,
                      Start_Vertex => FA.Start_Vertex,
                      End_Vertex   => FA.End_Vertex);
      end if;

      Data_Dependence_Graph.Create (FA);
      Control_Dependence_Graph.Create (FA);
      Interprocedural.Create (FA);
      Program_Dependence_Graph.Create (FA);

      --  Now we print everything else.
      if Debug_Flag_Dot_ZZ then
         if Debug_Print_Intermediates then
            Print_Graph (Filename     => Get_Name_String (Chars (E)) & "_ddg",
                         G            => FA.DDG,
                         Start_Vertex => FA.Start_Vertex,
                         End_Vertex   => FA.End_Vertex);

            Print_Graph (Filename     => Get_Name_String (Chars (E)) & "_cdg",
                         G            => FA.CDG,
                         Start_Vertex => FA.Start_Vertex,
                         End_Vertex   => FA.End_Vertex);
         end if;

         if Debug_Print_PDG then
            Print_Graph (Filename     => Get_Name_String (Chars (E)) & "_pdg",
                         G            => FA.PDG,
                         Start_Vertex => FA.Start_Vertex,
                         End_Vertex   => FA.End_Vertex);
         end if;
      end if;

      return FA;
   end Flow_Analyse_Entity;

   ------------------------
   -- Flow_Analyse_CUnit --
   ------------------------

   procedure Flow_Analyse_CUnit is
      FA_Graphs : Analysis_Maps.Map;
   begin
      --  Process entities and construct graphs if necessary
      for E of Spec_Entities loop
         if Ekind (E) in Subprogram_Kind and then Body_In_Alfa (E) then
            FA_Graphs.Include (E, Flow_Analyse_Entity (E));
         end if;
      end loop;

      for E of Body_Entities loop
         if Ekind (E) in Subprogram_Kind and then Body_In_Alfa (E) then
            FA_Graphs.Include (E, Flow_Analyse_Entity (E));
         end if;
      end loop;

      --  TODO: Perform interprocedural analysis

      --  Analyse graphs and produce error messages
      if Debug_Flag_Dot_ZZ then
         Output.Write_Str (Character'Val (8#33#) & "[32m" &
                             "Flow analysis (errors)" &
                             Character'Val (8#33#) & "[0m");
         Output.Write_Eol;
      end if;
      for FA of FA_Graphs loop
         Analysis.Sanity_Check (FA);
         Analysis.Find_Ineffective_Imports (FA);
         Analysis.Find_Illegal_Updates (FA);
         Analysis.Find_Ineffective_Statements (FA);
         Analysis.Find_Use_Of_Uninitialised_Variables (FA);
         Analysis.Find_Stable_Elements (FA);
      end loop;

   end Flow_Analyse_CUnit;

end Flow;
