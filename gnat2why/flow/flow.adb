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

with Ada.Characters.Latin_1;
with Ada.Strings;           use Ada.Strings;
with Ada.Strings.Maps;
with Ada.Strings.Unbounded; use Ada.Strings.Unbounded;

with Aspects;               use Aspects;
with Namet;                 use Namet;
with Nlists;                use Nlists;
with Sem_Util;              use Sem_Util;
with Snames;                use Snames;
with Sprint;                use Sprint;
with Sinfo;                 use Sinfo;

with Output;
with Treepr;                use Treepr;

with Why;
with SPARK_Definition;      use SPARK_Definition;
with SPARK_Util;

with Gnat2Why.Opt;

with Flow.Analysis;
with Flow.Control_Dependence_Graph;
with Flow.Control_Flow_Graph;
with Flow.Data_Dependence_Graph;
with Flow.Interprocedural;
with Flow.Program_Dependence_Graph;
with Flow_Tree_Utility;
with Flow.Utility;

use type Ada.Containers.Count_Type;

package body Flow is

   --  These debug options control which graphs to output.

   Debug_Print_CFG           : constant Boolean := True;
   Debug_Print_Intermediates : constant Boolean := False;
   Debug_Print_PDG           : constant Boolean := True;

   --  These debug options print certain bits of the datastructures
   --  calculated.

   Debug_Print_Magic_Source_Set : constant Boolean := False;
   --  Enable this to visualise the magic_source set.

   ------------------------------------------------------------

   use Flow_Graphs;

   Temp_String : Unbounded_String := Null_Unbounded_String;

   Whitespace : constant Ada.Strings.Maps.Character_Set :=
     Ada.Strings.Maps.To_Set
       (" " & Ada.Characters.Latin_1.CR & Ada.Characters.Latin_1.LF);

   procedure Add_To_Temp_String (S : String);
   --  Nasty nasty hack to add the given string to a global variable,
   --  Temp_String. We use this to pretty print nodes via Sprint_Node.

   function Calculate_Magic_Mapping
     (N : Node_Id)
      return Magic_String_To_Node_Sets.Map;
   --  Traverse the tree rooted at N, making a note of each function
   --  and procedure call which introduces a Magic_String
   --  Flow_Id. This is used for emitting more helpful error messages
   --  if a Magic_String Flow_Id is concerened.

   function Flow_Analyse_Entity (E : Entity_Id) return Flow_Analysis_Graphs
   with Pre =>
     (Ekind (E) in Subprogram_Kind and then Subprogram_Body_In_SPARK (E));
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

   -----------------------------
   -- Calculate_Magic_Mapping --
   -----------------------------

   function Calculate_Magic_Mapping
     (N : Node_Id)
      return Magic_String_To_Node_Sets.Map
   is
      use type Flow_Id_Sets.Set;

      RV : Magic_String_To_Node_Sets.Map;

      function Proc (N : Node_Id) return Traverse_Result;
      --  Update mapping if N is a function or procedure call.

      function Proc (N : Node_Id) return Traverse_Result is
         Global_Reads  : Flow_Id_Sets.Set;
         Global_Writes : Flow_Id_Sets.Set;
         Tmp           : Flow_Id;
         Globals       : Flow_Id_Sets.Set;
      begin
         case Nkind (N) is
            when N_Function_Call | N_Procedure_Call_Statement =>
               declare
                  Subprogram : constant Entity_Id := Entity (Name (N));
               begin
                  case Ekind (Subprogram) is
                     when E_Procedure | E_Function =>
                        Get_Globals (Subprogram => Subprogram,
                                     Reads      => Global_Reads,
                                     Writes     => Global_Writes);
                        Globals := Global_Reads or Global_Writes;

                        for F of Globals loop
                           if F.Kind = Magic_String then
                              Tmp := Change_Variant (F, Normal_Use);
                              if RV.Contains (Tmp.Name) then
                                 RV (Tmp.Name).Include (Subprogram);
                              else
                                 RV.Include (Tmp.Name,
                                             Node_Sets.To_Set (Subprogram));
                              end if;
                           end if;
                        end loop;

                     when E_Generic_Procedure | E_Generic_Function =>
                        return Skip;

                     when others =>
                        raise Why.Unexpected_Node;
                  end case;
               end;

            when others =>
               null;
         end case;

         return OK;
      end Proc;

      procedure Traverse is new Traverse_Proc (Proc);

   begin
      RV := Magic_String_To_Node_Sets.Empty_Map;
      Traverse (N);
      return RV;
   end Calculate_Magic_Mapping;

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
      if not Present (N) then
         return Empty;
      end if;
      pragma Assert (Nkind (N) = N_Iteration_Scheme);

      N := Loop_Parameter_Specification (N);
      if not Present (N) then
         return Empty;
      end if;
      pragma Assert (Nkind (N) = N_Loop_Parameter_Specification);

      return Defining_Identifier (N);
   end Loop_Parameter_From_Loop;

   -----------------
   -- Get_Globals --
   -----------------

   procedure Get_Globals (Subprogram             : Entity_Id;
                          Reads                  : out Flow_Id_Sets.Set;
                          Writes                 : out Flow_Id_Sets.Set;
                          Consider_Discriminants : Boolean := False)
   is
   begin
      Reads  := Flow_Id_Sets.Empty_Set;
      Writes := Flow_Id_Sets.Empty_Set;

      if Has_Aspect (Subprogram, Aspect_Global) then
         declare
            Global : constant Node_Id :=
              Get_Pragma (Subprogram, Pragma_Global);
            pragma Assert
              (List_Length (Pragma_Argument_Associations (Global)) = 1);

            PAA : constant Node_Id :=
              First (Pragma_Argument_Associations (Global));
            pragma Assert (Nkind (PAA) = N_Pragma_Argument_Association);

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
                     if Consider_Discriminants and then
                       Flow.Utility.Contains_Discriminants
                       (Direct_Mapping_Id (The_Global, In_View))
                     then
                        Reads.Insert (Direct_Mapping_Id
                                        (The_Global, In_View));
                     end if;
                     Writes.Insert (Direct_Mapping_Id
                                      (The_Global, Out_View));
                  when others =>
                     raise Program_Error;
               end case;
            end Process;
         begin
            if Nkind (Expression (PAA)) = N_Null then
               --  global => null
               --  No globals, nothing to do.
               return;

            elsif Nkind (Expression (PAA)) in
              N_Identifier | N_Expanded_Name
            then
               --  global => foo
               --  A single input
               Process (Name_Input, Entity (Expression (PAA)));

            elsif Nkind (Expression (PAA)) = N_Aggregate and then
              Expressions (Expression (PAA)) /= No_List then
               --  global => (foo, bar)
               --  Inputs
               RHS := First (Expressions (Expression (PAA)));
               while Present (RHS) loop
                  case Nkind (RHS) is
                     when N_Identifier | N_Expanded_Name =>
                        Process (Name_Input, Entity (RHS));
                     when others =>
                        raise Why.Unexpected_Node;
                  end case;
                  RHS := Next (RHS);
               end loop;

            elsif Nkind (Expression (PAA)) = N_Aggregate and then
              Component_Associations (Expression (PAA)) /= No_List then
               --  global => (mode => foo,
               --             mode => (bar, baz))
               --  A mixture of things.

               declare
                  CA : constant List_Id :=
                    Component_Associations (Expression (PAA));
               begin
                  Row := First (CA);
                  while Present (Row) loop
                     pragma Assert (List_Length (Choices (Row)) = 1);
                     The_Mode := Chars (First (Choices (Row)));

                     RHS := Expression (Row);
                     case Nkind (RHS) is
                        when N_Aggregate =>
                           RHS := First (Expressions (RHS));
                           while Present (RHS) loop
                              Process (The_Mode, Entity (RHS));
                              RHS := Next (RHS);
                           end loop;
                        when N_Identifier | N_Expanded_Name =>
                           Process (The_Mode, Entity (RHS));
                        when N_Null =>
                           null;
                        when others =>
                           Print_Node_Subtree (RHS);
                           raise Why.Unexpected_Node;
                     end case;

                     Row := Next (Row);
                  end loop;
               end;

            else
               raise Why.Unexpected_Node;
            end if;
         end;
      else
         --  We don't have a global aspect, so we should look at the
         --  computed globals...

         declare
            ALI_Reads  : constant Name_Set.Set := Get_Reads (Subprogram);
            ALI_Writes : constant Name_Set.Set := Get_Writes (Subprogram);

            function Get_Flow_Id
              (Name : Entity_Name;
               View : Parameter_Variant)
               return Flow_Id;
            --  Return a suitable flow id for the unique_name of an
            --  entity. We try our best to get a direct mapping,
            --  resorting to the magic string only as a last resort.

            function Get_Flow_Id
              (Name : Entity_Name;
               View : Parameter_Variant)
               return Flow_Id is
            begin
               --  Look for a direct mapping first.
               for E of All_Entities loop
                  if Unique_Name (E) = Name.all then
                     return Direct_Mapping_Id (E, View);
                  end if;
               end loop;

               --  If none can be found, we fall back to the magic
               --  string.
               return Magic_String_Id (Name, View);
            end Get_Flow_Id;

         begin
            for R of ALI_Reads loop
               Reads.Include (Get_Flow_Id (R, In_View));
            end loop;

            for W of ALI_Writes loop
               --  This is not a mistake, we must assume that all
               --  values written may also not change or that they are
               --  only partially updated.
               --
               --  This also takes care of discriminants as every out
               --  is really an in out.
               Reads.Include (Get_Flow_Id (W, In_View));
               Writes.Include (Get_Flow_Id (W, Out_View));
            end loop;
         end;

      end if;

   end Get_Globals;

   -----------------
   -- Has_Depends --
   -----------------

   function Has_Depends (Subprogram : Entity_Id) return Boolean is
   begin
      return Has_Aspect (Subprogram, Aspect_Depends);
   end Has_Depends;

   -----------------
   -- Get_Depends --
   -----------------

   procedure Get_Depends (Subprogram : Entity_Id;
                          Depends    : out Dependency_Maps.Map) is
      Depends_Contract : constant Node_Id :=
        Get_Pragma (Subprogram, Pragma_Depends);
      pragma Assert
        (List_Length (Pragma_Argument_Associations (Depends_Contract)) = 1);

      PAA : constant Node_Id :=
        First (Pragma_Argument_Associations (Depends_Contract));
      pragma Assert (Nkind (PAA) = N_Pragma_Argument_Association);

      CA : List_Id;

      Row : Node_Id;
      LHS : Node_Id;
      RHS : Node_Id;

      Inputs  : Flow_Id_Sets.Set;
      Outputs : Flow_Id_Sets.Set;

   begin
      Depends := Dependency_Maps.Empty_Map;

      if Ekind (Subprogram) = E_Function then
         --  ??? To be implemented by M412-008
         raise Why.Not_Implemented;
      end if;

      case Nkind (Expression (PAA)) is
         when N_Null =>
            --  Depends => null
            return;
         when N_Aggregate =>
            CA := Component_Associations (Expression (PAA));
         when others =>
            raise Why.Unexpected_Node;
      end case;

      Row := First (CA);
      while Present (Row) loop
         Inputs  := Flow_Id_Sets.Empty_Set;
         Outputs := Flow_Id_Sets.Empty_Set;

         LHS := First (Choices (Row));
         case Nkind (LHS) is
            when N_Aggregate =>
               LHS := First (Expressions (LHS));
               while Present (LHS) loop
                  pragma Assert (Present (Entity (LHS)));
                  Outputs.Include
                    (Direct_Mapping_Id (Unique_Entity (Entity (LHS))));
                  LHS := Next (LHS);
               end loop;
            when N_Identifier | N_Expanded_Name =>
               pragma Assert (Present (Entity (LHS)));
               Outputs.Include
                 (Direct_Mapping_Id (Unique_Entity (Entity (LHS))));
            when N_Null =>
               null;
            when others =>
               Print_Node_Subtree (LHS);
               raise Why.Unexpected_Node;
         end case;

         RHS := Expression (Row);
         case Nkind (RHS) is
            when N_Aggregate =>
               RHS := First (Expressions (RHS));
               while Present (RHS) loop
                  pragma Assert (Present (Entity (RHS)));
                  Inputs.Include
                    (Direct_Mapping_Id (Unique_Entity (Entity (RHS))));
                  RHS := Next (RHS);
               end loop;
            when N_Identifier | N_Expanded_Name =>
               pragma Assert (Present (Entity (RHS)));
               Inputs.Include
                 (Direct_Mapping_Id (Unique_Entity (Entity (RHS))));
            when N_Null =>
               null;
            when others =>
               Print_Node_Subtree (RHS);
               raise Why.Unexpected_Node;
         end case;

         if Outputs.Length = 0 and then Inputs.Length >= 1 then
            --  The inser is on purpose - we want this to fail if we
            --  manage to obtain more than one null derives.
            Depends.Insert (Null_Flow_Id, Flow_Id_Sets.Empty_Set);
            for Input of Inputs loop
               Depends (Null_Flow_Id).Include (Input);
            end loop;
         else
            for Output of Outputs loop
               Depends.Include (Output, Flow_Id_Sets.Empty_Set);
               for Input of Inputs loop
                  Depends (Output).Include (Input);
               end loop;
            end loop;
         end if;

         Row := Next (Row);
      end loop;

   end Get_Depends;

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
                  pragma Assert (A.Parameter_Formal.Kind = Direct_Mapping);
                  pragma Assert (A.Parameter_Actual.Kind = Direct_Mapping);
                  Sprint_Node (A.Parameter_Formal.Node);
                  Output.Write_Str ("'in");
                  Output.Write_Str ("&nbsp;:=&nbsp;");
                  Sprint_Node (A.Parameter_Actual.Node);
                  if A.Is_Discriminants_Only_Parameter then
                     Output.Write_Str ("'discriminants");
                  end if;

               when Out_View =>
                  pragma Assert (A.Parameter_Formal.Kind = Direct_Mapping);
                  pragma Assert (A.Parameter_Actual.Kind = Direct_Mapping);
                  pragma Assert (not A.Is_Discriminants_Only_Parameter);
                  Sprint_Node (A.Parameter_Actual.Node);
                  Output.Write_Str ("&nbsp;:=&nbsp;");
                  Sprint_Node (A.Parameter_Formal.Node);
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
                  if A.Is_Discriminants_Only_Parameter then
                     Output.Write_Str ("'discriminants");
                  end if;
                  Output.Write_Str ("'in");

               when Out_View =>
                  pragma Assert (not A.Is_Discriminants_Only_Parameter);
                  Output.Write_Str ("'out");

               when others =>
                  raise Program_Error;
            end case;

         elsif A.Is_Default_Init then
            Rv.Shape := Shape_None;

            Sprint_Flow_Id (A.Default_Init_Var);
            Output.Write_Str ("&nbsp;is by default&nbsp;");
            Sprint_Node (A.Default_Init_Val);

         else
            if A.Is_Precondition then
               Rv.Shape := Shape_None;
               Output.Write_Str ("precondition ");
            elsif A.Is_Loop_Entry then
               Rv.Shape := Shape_None;
               Output.Write_Str ("loop entry ");
            end if;

            case F.Kind is
               when Direct_Mapping =>
                  declare
                     N : constant Node_Id := Get_Direct_Mapping_Id (F);
                  begin
                     case Nkind (N) is
                        when N_Case_Statement =>
                           Rv.Shape := Shape_Diamond;
                           Output.Write_Str ("case ");
                           Sprint_Node (Expression (N));

                        when N_Case_Statement_Alternative =>
                           Rv.Shape := Shape_None;
                           Output.Write_Str ("when ");
                           Sprint_Comma_List (Discrete_Choices (N));

                        when N_Elsif_Part =>
                           Rv.Shape := Shape_Diamond;
                           Output.Write_Str ("elsif ");
                           Sprint_Node (Condition (N));

                        when N_If_Statement =>
                           Rv.Shape := Shape_Diamond;
                           Output.Write_Str ("if ");
                           Sprint_Node (Condition (N));

                        when N_Loop_Statement =>
                           Rv.Shape := Shape_Diamond;
                           if not Present (Iteration_Scheme (N)) then
                              --  Basic loop. Should never
                              --  appear as a vertex in the
                              --  graph.
                              pragma Assert (False);
                           elsif Present
                             (Condition (Iteration_Scheme (N)))
                           then
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

               when Record_Field | Magic_String =>
                  Sprint_Flow_Id (F);

               when others =>
                  raise Why.Unexpected_Node;
            end case;

            case F.Variant is
               when Initial_Grouping =>
                  Rv.Shape := Shape_None;
                  Output.Write_Str ("'group'initial");

               when Final_Grouping =>
                  Rv.Shape := Shape_None;
                  Output.Write_Str ("'group'final");

               when Initial_Value =>
                  Rv.Shape := Shape_None;
                  Output.Write_Str ("'initial");

                  if not A.Is_Initialised then
                     Rv.Colour := To_Unbounded_String ("red");
                  elsif Flow.Utility.Is_Discriminant (F) then
                     Rv.Colour := To_Unbounded_String ("purple");
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
      if Gnat2Why.Opt.Flow_Dump_Graphs then
         G.Write_Pdf_File
           (Filename  => Filename,
            Node_Info => NDI'Access,
            Edge_Info => EDI'Access);
      else
         G.Write_Dot_File
           (Filename  => Filename,
            Node_Info => NDI'Access,
            Edge_Info => EDI'Access);
      end if;
   end Print_Graph;

   -------------------------
   -- Flow_Analyse_Entity --
   -------------------------

   function Flow_Analyse_Entity (E : Entity_Id) return Flow_Analysis_Graphs is
      Body_N : constant Node_Id := SPARK_Util.Get_Subprogram_Body (E);
      FA     : Flow_Analysis_Graphs;
   begin
      FA := Flow_Analysis_Graphs'
        (Subprogram       => E,
         Start_Vertex     => Null_Vertex,
         End_Vertex       => Null_Vertex,
         CFG              => Create,
         DDG              => Create,
         CDG              => Create,
         TDG              => Create,
         PDG              => Create,
         All_Vars         => Flow_Id_Sets.Empty_Set,
         Loops            => Node_Sets.Empty_Set,
         Magic_Source     => Calculate_Magic_Mapping (Body_N),
         Aliasing_Present => False,
         Is_Main          => Flow_Tree_Utility.Might_Be_Main (E));

      if Debug_Print_Magic_Source_Set then
         for C in FA.Magic_Source.Iterate loop
            Output.Write_Str (Magic_String_To_Node_Sets.Key (C).all);
            Output.Write_Eol;

            Output.Indent;
            for E of Magic_String_To_Node_Sets.Element (C) loop
               Sprint_Node (E);
               Output.Write_Eol;
            end loop;
            Output.Outdent;
         end loop;
      end if;

      if Gnat2Why.Opt.Flow_Dump_Graphs then
         Output.Write_Str (Character'Val (8#33#) & "[32m" &
                             "Flow analysis (cons) of " &
                             Get_Name_String (Chars (E)) &
                             Character'Val (8#33#) & "[0m");
         Output.Write_Eol;
      end if;
      Control_Flow_Graph.Create (Body_N, FA);

      --  We print this graph first in cast the other algorithms
      --  barf.
      if Debug_Print_CFG then
         Print_Graph (Filename     => Get_Name_String (Chars (E)) & "_cfg",
                      G            => FA.CFG,
                      Start_Vertex => FA.Start_Vertex,
                      End_Vertex   => FA.End_Vertex);
      end if;

      Control_Dependence_Graph.Create (FA);

      if Debug_Print_Intermediates then
         Print_Graph (Filename     => Get_Name_String (Chars (E)) & "_cdg",
                      G            => FA.CDG,
                      Start_Vertex => FA.Start_Vertex,
                      End_Vertex   => FA.End_Vertex);
      end if;

      Data_Dependence_Graph.Create (FA);
      Interprocedural.Create (FA);
      Program_Dependence_Graph.Create (FA);

      if Debug_Print_Intermediates then
         Print_Graph (Filename     => Get_Name_String (Chars (E)) & "_ddg",
                      G            => FA.DDG,
                      Start_Vertex => FA.Start_Vertex,
                      End_Vertex   => FA.End_Vertex);
      end if;

      if Debug_Print_PDG then
         Print_Graph (Filename     => Get_Name_String (Chars (E)) & "_pdg",
                      G            => FA.PDG,
                      Start_Vertex => FA.Start_Vertex,
                      End_Vertex   => FA.End_Vertex);
      end if;

      return FA;
   end Flow_Analyse_Entity;

   ------------------------
   -- Flow_Analyse_CUnit --
   ------------------------

   procedure Flow_Analyse_CUnit is
      FA_Graphs : Analysis_Maps.Map;
      Success   : Boolean;
   begin
      --  Process entities and construct graphs if necessary
      for E of Spec_Entities loop
         if Ekind (E) in Subprogram_Kind
           and then Subprogram_Body_In_SPARK (E)
         then
            FA_Graphs.Include (E, Flow_Analyse_Entity (E));
         end if;
      end loop;

      for E of Body_Entities loop
         if Ekind (E) in Subprogram_Kind
           and then Subprogram_Body_In_SPARK (E)
         then
            FA_Graphs.Include (E, Flow_Analyse_Entity (E));
         end if;
      end loop;

      --  TODO: Perform interprocedural analysis

      --  Analyse graphs and produce error messages
      for FA of FA_Graphs loop
         if Gnat2Why.Opt.Flow_Dump_Graphs then
            Output.Write_Str (Character'Val (8#33#) & "[32m" &
                                "Flow analysis (errors) for " &
                                Get_Name_String (Chars (FA.Subprogram)) &
                                Character'Val (8#33#) & "[0m");
            Output.Write_Eol;
         end if;
         Analysis.Sanity_Check (FA, Success);
         if Success then
            Analysis.Find_Ineffective_Imports (FA);
            Analysis.Find_Illegal_Updates (FA);
            Analysis.Find_Ineffective_Statements (FA);
            Analysis.Find_Use_Of_Uninitialised_Variables (FA);
            Analysis.Find_Stable_Elements (FA);
            Analysis.Find_Unused_Objects (FA);
            Analysis.Check_Contracts (FA);
            Analysis.Analyse_Main (FA);
         end if;
      end loop;

   end Flow_Analyse_CUnit;

end Flow;
