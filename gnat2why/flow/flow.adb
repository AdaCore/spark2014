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
with Ada.Strings;                   use Ada.Strings;
with Ada.Strings.Maps;

with Errout;                        use Errout;
with Lib;                           use Lib;
with Namet;                         use Namet;
with Osint;                         use Osint;
with Sem_Ch7;                       use Sem_Ch7;
with Sem_Util;                      use Sem_Util;
with Sinfo;                         use Sinfo;
with Snames;                        use Snames;
with Sprint;                        use Sprint;

with Output;                        use Output;
with Treepr;                        use Treepr;

with Why;
with SPARK_Definition;              use SPARK_Definition;
with SPARK_Util;

with Gnat2Why_Args;
with GNAT.Directory_Operations;     use GNAT.Directory_Operations;

with Flow.Analysis;
with Flow.Control_Dependence_Graph;
with Flow.Control_Flow_Graph;
with Flow.Data_Dependence_Graph;
with Flow.Interprocedural;
with Flow.Program_Dependence_Graph;

with Flow.Utility;                  use Flow.Utility;
with Flow_Error_Messages;           use Flow_Error_Messages;
with Flow.Slice;                    use Flow.Slice;

use type Ada.Containers.Count_Type;

package body Flow is

   --  These debug options control which graphs to output.

   Debug_Print_CFG           : constant Boolean := True;
   Debug_Print_Intermediates : constant Boolean := False;
   Debug_Print_PDG           : constant Boolean := True;

   --  These debug options control some of the tracing produced.

   Debug_Trace_Scoping : constant Boolean := False;

   ------------------------------------------------------------

   use Flow_Graphs;

   Temp_String : Unbounded_String := Null_Unbounded_String;

   Whitespace : constant Ada.Strings.Maps.Character_Set :=
     Ada.Strings.Maps.To_Set
       (" " & Ada.Characters.Latin_1.CR & Ada.Characters.Latin_1.LF);

   procedure Add_To_Temp_String (S : String);
   --  Nasty nasty hack to add the given string to a global variable,
   --  Temp_String. We use this to pretty print nodes via Sprint_Node.

   function Flow_Analyse_Entity (E : Entity_Id;
                                 S : Node_Id)
                                 return Flow_Analysis_Graphs
     with Pre  => Ekind (E) in Subprogram_Kind | E_Package | E_Package_Body,
          Post => Is_Valid (Flow_Analyse_Entity'Result);
   --  Flow analyse the given entity E. S should be the node
   --  representing the specification of E (i.e. where the N_Contract
   --  node is attached). This subprogram does nothing for entities
   --  without a body and not in SPARK 2014.

   -------------------------
   -- Add_To_Temp_String  --
   -------------------------

   procedure Add_To_Temp_String (S : String) is
   begin
      Append
        (Temp_String,
         Trim (To_Unbounded_String (S), Whitespace, Whitespace));
   end Add_To_Temp_String;

   --------------
   -- Is_Valid --
   --------------

   function Is_Valid (X : Flow_Analysis_Graphs_Root)
                      return Boolean
   is (case X.Kind is
          when E_Subprogram_Body =>
             Ekind (X.Analyzed_Entity) in E_Function | E_Procedure,
          when E_Package =>
             Ekind (X.Analyzed_Entity) = E_Package,
          when E_Package_Body =>
             Ekind (X.Analyzed_Entity) = E_Package_Body
      );

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
   -- Has_Depends --
   -----------------

   function Has_Depends (Subprogram : Entity_Id) return Boolean is
   begin
      return Present (Get_Pragma (Subprogram, Pragma_Depends));
   end Has_Depends;

   -------------------------
   -- Has_Refined_Depends --
   -------------------------

   function Has_Refined_Depends (Subprogram : Entity_Id) return Boolean is
      Body_N : constant Node_Id := Get_Subprogram_Body (Subprogram);
   begin
      if Present (Body_N) then
         if Acts_As_Spec (Body_N) then
            return Present (Get_Pragma (Subprogram, Pragma_Refined_Depends));
         else
            return Present (Get_Pragma (Get_Body (Subprogram),
                                        Pragma_Refined_Depends));
         end if;
      else
         return False;
      end if;
   end Has_Refined_Depends;

   -----------------
   -- Get_Depends --
   -----------------

   procedure Get_Depends (Subprogram : Entity_Id;
                          Refined    : Boolean;
                          Depends    : out Dependency_Maps.Map)
   is
      Body_N : constant Node_Id := Get_Subprogram_Body (Subprogram);
      Deps   : Node_Id          := Empty;
   begin
      if Refined and then Present (Body_N) then
         if Acts_As_Spec (Body_N) then
            Deps := Get_Pragma (Subprogram, Pragma_Refined_Depends);
         else
            Deps := Get_Pragma (Get_Body (Subprogram), Pragma_Refined_Depends);
         end if;
      end if;
      if not Present (Deps) then
         Deps := Get_Pragma (Subprogram, Pragma_Depends);
      end if;
      pragma Assert (Present (Deps));
      Depends := Parse_Depends (Deps);
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
         Set_Special_Output (Add_To_Temp_String'Access);

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
                  Write_Str ("'in");
                  Write_Str ("&nbsp;:=&nbsp;");
                  Sprint_Node (A.Parameter_Actual.Node);
                  if A.Is_Discriminants_Only_Parameter then
                     Write_Str ("'discriminants");
                  end if;

               when Out_View =>
                  pragma Assert (A.Parameter_Formal.Kind = Direct_Mapping);
                  pragma Assert (A.Parameter_Actual.Kind = Direct_Mapping);
                  pragma Assert (not A.Is_Discriminants_Only_Parameter);
                  Sprint_Node (A.Parameter_Actual.Node);
                  Write_Str ("&nbsp;:=&nbsp;");
                  Sprint_Node (A.Parameter_Formal.Node);
                  Write_Str ("'out");

               when others =>
                  raise Program_Error;
            end case;

         elsif A.Is_Global_Parameter then
            Rv.Shape := Shape_None;

            Write_Str ("global&nbsp;");
            Sprint_Flow_Id (A.Parameter_Formal);
            case A.Parameter_Formal.Variant is
               when In_View =>
                  if A.Is_Discriminants_Only_Parameter then
                     Write_Str ("'discriminants");
                  end if;
                  Write_Str ("'in");

               when Out_View =>
                  pragma Assert (not A.Is_Discriminants_Only_Parameter);
                  Write_Str ("'out");

               when others =>
                  raise Program_Error;
            end case;

         elsif A.Is_Default_Init then
            Rv.Shape := Shape_None;

            Sprint_Flow_Id (A.Default_Init_Var);
            Write_Str ("&nbsp;is by default&nbsp;");
            Sprint_Node (A.Default_Init_Val);

         else
            if A.Is_Precondition then
               Rv.Shape := Shape_None;
               Write_Str ("precondition ");
            elsif A.Is_Loop_Entry then
               Rv.Shape := Shape_None;
               Write_Str ("loop entry ");
            end if;

            case F.Kind is
               when Direct_Mapping =>
                  declare
                     N : constant Node_Id := Get_Direct_Mapping_Id (F);
                  begin
                     case Nkind (N) is
                        when N_Case_Statement =>
                           Rv.Shape := Shape_Diamond;
                           Write_Str ("case ");
                           Sprint_Node (Expression (N));

                        when N_Case_Statement_Alternative =>
                           Rv.Shape := Shape_None;
                           Write_Str ("when ");
                           Sprint_Comma_List (Discrete_Choices (N));

                        when N_Defining_Identifier =>
                           case Ekind (N) is
                              when E_Return_Statement =>
                                 Write_Str ("return ");
                                 Sprint_Node (A.Aux_Node);

                              when others =>
                                 Sprint_Node (N);
                           end case;

                        when N_Elsif_Part =>
                           Rv.Shape := Shape_Diamond;
                           Write_Str ("elsif ");
                           Sprint_Node (Condition (N));

                        when N_If_Statement =>
                           Rv.Shape := Shape_Diamond;
                           Write_Str ("if ");
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
                              Write_Str ("while ");
                              Sprint_Node
                                (Condition (Iteration_Scheme (N)));
                           else
                              Sprint_Node
                                (Iteration_Scheme (N));
                           end if;

                        when N_Procedure_Call_Statement =>
                           Rv.Shape := Shape_Box;
                           Write_Str ("call ");
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
                  Write_Str ("'group'initial");

               when Final_Grouping =>
                  Rv.Shape := Shape_None;
                  Write_Str ("'group'final");

               when Initial_Value =>
                  Rv.Shape := Shape_None;
                  Write_Str ("'initial");

                  if not A.Is_Initialised then
                     Rv.Colour := To_Unbounded_String ("red");
                  elsif Is_Discriminant (F) then
                     Rv.Colour := To_Unbounded_String ("purple");
                  end if;

               when Final_Value =>
                  Rv.Shape := Shape_None;
                  Write_Str ("'final");
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
               Write_Str ("\nLoops:");
               for Loop_Identifier of A.Loops loop
                  Write_Str ("&nbsp;");
                  Sprint_Node (Loop_Identifier);
               end loop;
            end if;

            if A.Perform_IPFA then
               Write_Str ("\nIPFA");
            end if;

            if A.Is_Global then
               Write_Str ("\n(global)");
            end if;
         end if;

         Write_Eol;
         Cancel_Special_Output;

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
      if Gnat2Why_Args.Flow_Debug_Mode then
         if Gnat2Why_Args.Flow_Advanced_Debug then
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
      end if;
   end Print_Graph;

   -------------------------
   -- Flow_Analyse_Entity --
   -------------------------

   function Flow_Analyse_Entity (E : Entity_Id;
                                 S : Node_Id)
                                 return Flow_Analysis_Graphs
   is
      FA : Flow_Analysis_Graphs;
   begin
      case Ekind (E) is
         when Subprogram_Kind =>
            FA := Flow_Analysis_Graphs'
              (Kind              => E_Subprogram_Body,
               Analyzed_Entity   => E,
               Scope             => SPARK_Util.Get_Subprogram_Body (E),
               Spec_Scope        => Get_Enclosing_Scope (E),
               Spec_Node         => S,
               Start_Vertex      => Null_Vertex,
               End_Vertex        => Null_Vertex,
               CFG               => Create,
               DDG               => Create,
               CDG               => Create,
               TDG               => Create,
               PDG               => Create,
               All_Vars          => Flow_Id_Sets.Empty_Set,
               Unmodified_Vars   => Node_Sets.Empty_Set,
               Unreferenced_Vars => Node_Sets.Empty_Set,
               Loops             => Node_Sets.Empty_Set,
               Aliasing_Present  => False,
               Dependency_Map    => Dependency_Maps.Empty_Map,
               Base_Filename     => To_Unbounded_String ("subprogram_"),
               Is_Main           => Might_Be_Main (E),
               Is_Generative     => not (Present
                                           (Get_Pragma (E, Pragma_Global)) or
                                         Present
                                           (Get_Pragma (E, Pragma_Depends))),
               Last_Statement_Is_Raise => Last_Statement_Is_Raise (E),
               Depends_N         => Empty,
               Refined_Depends_N => Empty,
               Function_Side_Effects_Present => False);

         when E_Package =>
            FA := Flow_Analysis_Graphs'
              (Kind              => E_Package,
               Analyzed_Entity   => E,
               Scope             => Get_Enclosing_Scope (E),
               Spec_Scope        => Get_Enclosing_Scope (E),
               Spec_Node         => S,
               Start_Vertex      => Null_Vertex,
               End_Vertex        => Null_Vertex,
               CFG               => Create,
               DDG               => Create,
               CDG               => Create,
               TDG               => Create,
               PDG               => Create,
               All_Vars          => Flow_Id_Sets.Empty_Set,
               Unmodified_Vars   => Node_Sets.Empty_Set,
               Unreferenced_Vars => Node_Sets.Empty_Set,
               Loops             => Node_Sets.Empty_Set,
               Aliasing_Present  => False,
               Dependency_Map    => Dependency_Maps.Empty_Map,
               Base_Filename     => To_Unbounded_String ("package_spec_"),
               Initializes_N     => Empty,
               Visible_Vars      => Flow_Id_Sets.Empty_Set);

         when E_Package_Body =>
            FA := Flow_Analysis_Graphs'
              (Kind              => E_Package_Body,
               Analyzed_Entity   => E,
               Scope             => Get_Enclosing_Body_Scope (E),
               Spec_Scope        => Get_Enclosing_Scope (S),
               Spec_Node         => S,
               Start_Vertex      => Null_Vertex,
               End_Vertex        => Null_Vertex,
               CFG               => Create,
               DDG               => Create,
               CDG               => Create,
               TDG               => Create,
               PDG               => Create,
               All_Vars          => Flow_Id_Sets.Empty_Set,
               Unmodified_Vars   => Node_Sets.Empty_Set,
               Unreferenced_Vars => Node_Sets.Empty_Set,
               Loops             => Node_Sets.Empty_Set,
               Aliasing_Present  => False,
               Dependency_Map    => Dependency_Maps.Empty_Map,
               Base_Filename     => To_Unbounded_String ("package_body_"),
               Initializes_N     => Empty,
               Visible_Vars      => Flow_Id_Sets.Empty_Set);

         when others =>
            raise Why.Not_SPARK;
      end case;
      pragma Assert (Is_Valid (FA));

      Append (FA.Base_Filename, Get_Name_String (Chars (E)));

      if Gnat2Why_Args.Flow_Advanced_Debug then
         Write_Str (Character'Val (8#33#) & "[32m" &
                      "Flow analysis (cons) of " &
                      Entity_Kind'Image (FA.Kind) &
                      " " &
                      Character'Val (8#33#) & "[1m" &
                      Get_Name_String (Chars (E)) &
                      Character'Val (8#33#) & "[0m");
         Write_Eol;

         if Debug_Trace_Scoping then
            Indent;
            Write_Str ("Entity:     ");
            Print_Node_Briefly (FA.Analyzed_Entity);
            Write_Str ("Scope:      ");
            Print_Tree_Node (FA.Scope);
            Write_Str ("Spec_Scope: ");
            Print_Tree_Node (FA.Spec_Scope);
            Outdent;
         end if;
      end if;

      Control_Flow_Graph.Create (FA);

      --  We print this graph first in cast the other algorithms
      --  barf.
      if Debug_Print_CFG then
         Print_Graph (Filename     => To_String (FA.Base_Filename) & "_cfg",
                      G            => FA.CFG,
                      Start_Vertex => FA.Start_Vertex,
                      End_Vertex   => FA.End_Vertex);
      end if;

      Control_Dependence_Graph.Create (FA);

      if Debug_Print_Intermediates then
         Print_Graph (Filename     => To_String (FA.Base_Filename) & "_cdg",
                      G            => FA.CDG,
                      Start_Vertex => FA.Start_Vertex,
                      End_Vertex   => FA.End_Vertex);
      end if;

      Data_Dependence_Graph.Create (FA);
      Interprocedural.Create (FA);
      Program_Dependence_Graph.Create (FA);

      if Debug_Print_Intermediates then
         Print_Graph (Filename     => To_String (FA.Base_Filename) & "_ddg",
                      G            => FA.DDG,
                      Start_Vertex => FA.Start_Vertex,
                      End_Vertex   => FA.End_Vertex);
      end if;

      if Debug_Print_PDG then
         Print_Graph (Filename     => To_String (FA.Base_Filename) & "_pdg",
                      G            => FA.PDG,
                      Start_Vertex => FA.Start_Vertex,
                      End_Vertex   => FA.End_Vertex);
      end if;

      return FA;
   end Flow_Analyse_Entity;

   ------------------------
   -- Flow_Analyse_CUnit --
   ------------------------

   procedure Flow_Analyse_CUnit (GNAT_Root : Node_Id) is
      FA_Graphs : Analysis_Maps.Map;
      Success   : Boolean;

      function Analysis_Requested (E : Entity_Id) return Boolean;
      --  Returns true if entity E has to be analyzed.

      function Is_In_Analyzed_Files (E : Entity_Id) return Boolean;
      --  Returns true if E belongs to one of the entities that correspond
      --  to the files that are to be analyzed. If Analyze_Files is an empty
      --  list then we return true since we need to analyze everything.

      function Is_Requested_Subprogram (E : Entity_Id) return Boolean;
      --  Returns true if E is the entity corresponding to the single
      --  subprogram that needs to be analyzed, or if Gnat2Why_Args.Limit_Subp
      --  is the Null_Unbounded_String.

      ------------------------
      -- Analysis_Requested --
      ------------------------

      function Analysis_Requested (E : Entity_Id) return Boolean is
         (Is_In_Analyzed_Files (E) and then Is_Requested_Subprogram (E));

      --------------------------
      -- Is_In_Analyzed_Files --
      --------------------------

      function Is_In_Analyzed_Files (E : Entity_Id) return Boolean is
      begin
         --  If the entity is not in the compilation unit that is
         --  currently being analyzed then return false.
         if Cunit (Main_Unit) /= Enclosing_Comp_Unit_Node (E)
           and then Library_Unit (Cunit (Main_Unit)) /=
             Enclosing_Comp_Unit_Node (E)
         then
            return False;
         end if;

         --  If an empty files list has been provided then all entities that
         --  are in the compilation unit that is currently being analyzed must
         --  be analyzed.
         if Gnat2Why_Args.Analyze_File.Is_Empty then
            return True;
         end if;

         declare
            Spec_Prefix : constant String := Spec_File_Name (E);
            Body_Prefix : constant String := Body_File_Name (E);
         begin
            for A_File of Gnat2Why_Args.Analyze_File loop
               declare
                  Filename : constant String := File_Name (A_File);
               begin
                  if Filename = Body_Prefix or Filename = Spec_Prefix then
                     return True;
                  end if;
               end;
            end loop;
            return False;
         end;
      end Is_In_Analyzed_Files;

      -----------------------------
      -- Is_Requested_Subprogram --
      -----------------------------

      function Is_Requested_Subprogram (E : Entity_Id) return Boolean is
      begin
         if Gnat2Why_Args.Limit_Subp = Null_Unbounded_String then
            return True;
         end if;

         if Ekind (E) in Subprogram_Kind
           and then "GP_Subp:" & To_String (Gnat2Why_Args.Limit_Subp) =
           Gnat2Why.Nodes.Subp_Location (E)
         then
            return True;
         else
            return False;
         end if;
      end Is_Requested_Subprogram;
   begin
      --  Process entities and construct graphs if necessary
      for E of Entity_Set loop
         case Ekind (E) is
            when Subprogram_Kind =>
               if Analysis_Requested (E)
                 and Entity_Body_In_SPARK (E)
               then
                  FA_Graphs.Include (E, Flow_Analyse_Entity (E, E));
               end if;

            when E_Package =>
               declare
                  Pkg_Spec   : constant Node_Id := Get_Enclosing_Scope (E);
                  Pkg_Body   : Node_Id;
                  Needs_Body : Boolean := Unit_Requires_Body (E);
               begin
                  if Analysis_Requested (E)
                    and Entity_Spec_In_SPARK (E)
                    and not In_Predefined_Unit (E)
                  then
                     Pkg_Body := Pkg_Spec;
                     while Present (Pkg_Body) and
                       Nkind (Pkg_Body) /= N_Package_Declaration
                     loop
                        Pkg_Body := Parent (Pkg_Body);
                     end loop;
                     if Present (Pkg_Body) then
                        Pkg_Body := Corresponding_Body (Pkg_Body);
                     end if;

                     if Present (Pkg_Body) then
                        pragma Assert
                          (Nkind (Pkg_Body) = N_Defining_Identifier and then
                             Ekind (Pkg_Body) = E_Package_Body);
                        Needs_Body := True;
                     end if;

                     if Needs_Body and Entity_Body_In_SPARK (E) then
                        FA_Graphs.Include
                          (Pkg_Body,
                           Flow_Analyse_Entity (Pkg_Body, E));
                     elsif not Needs_Body then
                        FA_Graphs.Include (E, Flow_Analyse_Entity (E, E));
                     else
                        null;
                        --  ??? warning that we can't flow analyze
                        --      elaboration?
                     end if;

                  end if;
               end;

            when others =>
               null;
         end case;
      end loop;

      --  ??? Perform interprocedural analysis

      --  Analyse graphs and produce error messages
      for FA of FA_Graphs loop
         if Gnat2Why_Args.Flow_Advanced_Debug then
            Write_Str (Character'Val (8#33#) & "[32m" &
                         "Flow analysis (errors) for " &
                         Entity_Kind'Image (FA.Kind) &
                         " " &
                         Character'Val (8#33#) & "[1m" &
                         Get_Name_String (Chars (FA.Analyzed_Entity)) &
                         Character'Val (8#33#) & "[0m");
            Write_Eol;
         end if;

         Analysis.Sanity_Check (FA, Success);
         if Success then
            Analysis.Sanity_Check_Postcondition (FA, Success);
         end if;
         if Success then
            FA.Dependency_Map := Compute_Dependency_Relation (FA);

            case FA.Kind is
               when E_Subprogram_Body =>
                  Analysis.Find_Unwritten_Exports (FA);
                  Analysis.Find_Ineffective_Imports (FA);
                  Analysis.Find_Ineffective_Statements (FA);
                  Analysis.Find_Use_Of_Uninitialised_Variables (FA);
                  Analysis.Find_Unused_Objects (FA);
                  Analysis.Find_Exports_Derived_From_Proof_Ins (FA);
                  Analysis.Check_Contracts (FA);
                  Analysis.Analyse_Main (FA);

               when E_Package =>
                  Analysis.Find_Use_Of_Uninitialised_Variables (FA);
                  Analysis.Find_Ineffective_Statements (FA);
                  Analysis.Find_Use_Of_Uninitialised_Variables (FA);

               when E_Package_Body =>
                  Analysis.Find_Use_Of_Uninitialised_Variables (FA);
                  Analysis.Find_Ineffective_Statements (FA);
                  Analysis.Find_Use_Of_Uninitialised_Variables (FA);
            end case;
         end if;

      end loop;

      --  Create the "unit.flow" file that contains all emitted flow messages.
      Create_Flow_Msgs_File (GNAT_Root);

      if Gnat2Why_Args.Flow_Advanced_Debug then
         Write_Str (Character'Val (8#33#) & "[33m" &
                      "Flow analysis complete for current CU" &
                      Character'Val (8#33#) & "[0m");
         Write_Eol;
      end if;

      --  If an error was found then print all errors/warnings and return
      --  with an error status.

      if Found_Flow_Error then
         Errout.Finalize (Last_Call => True);
         Errout.Output_Messages;
         Exit_Program (E_Errors);
      end if;
   end Flow_Analyse_CUnit;

end Flow;
