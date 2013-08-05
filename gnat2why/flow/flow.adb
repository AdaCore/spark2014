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
with Ada.Strings;               use Ada.Strings;
with Ada.Strings.Maps;
with Ada.Text_IO;

with Namet;                     use Namet;
with Nlists;                    use Nlists;
with Sem_Util;                  use Sem_Util;
with Snames;                    use Snames;
with Sprint;                    use Sprint;
with Sinfo;                     use Sinfo;
with Sinput;                    use Sinput;
with Lib;                       use Lib;

with Output;                    use Output;
with Treepr;                    use Treepr;

with Why;
with SPARK_Definition;          use SPARK_Definition;
with SPARK_Util;

with Gnat2Why_Args;
with GNAT.Directory_Operations; use GNAT.Directory_Operations;

with Flow.Analysis;
with Flow.Control_Dependence_Graph;
with Flow.Control_Flow_Graph;
with Flow.Data_Dependence_Graph;
with Flow.Interprocedural;
with Flow.Program_Dependence_Graph;

with Flow.Utility;              use Flow.Utility;

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

   function Flow_Analyse_Entity (E : Entity_Id)
                                 return Flow_Analysis_Graphs
     with Pre  => Ekind (E) in Subprogram_Kind | E_Package | E_Package_Body,
          Post => Is_Valid (Flow_Analyse_Entity'Result);
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
               if Nkind (Name (N)) = N_Explicit_Dereference then
                  --  Deal with this non-spark case
                  return OK;
               end if;

               declare
                  Subprogram : constant Entity_Id := Entity (Name (N));
               begin
                  case Ekind (Subprogram) is
                     when E_Procedure | E_Function =>
                        for View in Boolean loop
                           Get_Globals (Subprogram   => Subprogram,
                                        Reads        => Global_Reads,
                                        Writes       => Global_Writes,
                                        Refined_View => View);
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
   -- Get_Globals --
   -----------------

   procedure Get_Globals (Subprogram             : Entity_Id;
                          Reads                  : out Flow_Id_Sets.Set;
                          Writes                 : out Flow_Id_Sets.Set;
                          Refined_View           : Boolean;
                          Consider_Discriminants : Boolean := False)
   is
      Has_Global_Aspect : Boolean;
      Global_Node       : Node_Id;
      Body_E            : constant Entity_Id := Get_Body (Subprogram);
   begin
      Reads  := Flow_Id_Sets.Empty_Set;
      Writes := Flow_Id_Sets.Empty_Set;

      if Refined_View and then Present (Body_E) and then
        Present (Get_Pragma (Body_E, Pragma_Refined_Global))
      then
         Has_Global_Aspect := True;
         Global_Node       := Get_Pragma (Body_E, Pragma_Refined_Global);

      elsif Present (Get_Pragma (Subprogram, Pragma_Global)) then
         Has_Global_Aspect := True;
         Global_Node       := Get_Pragma (Subprogram, Pragma_Global);

      else
         Has_Global_Aspect := False;
      end if;

      if Has_Global_Aspect then
         declare
            pragma Assert
              (List_Length (Pragma_Argument_Associations (Global_Node)) = 1);

            PAA : constant Node_Id :=
              First (Pragma_Argument_Associations (Global_Node));
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
                       Contains_Discriminants
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
      return Present (Get_Pragma (Subprogram, Pragma_Depends));
   end Has_Depends;

   -----------------
   -- Get_Depends --
   -----------------

   procedure Get_Depends (Subprogram : Entity_Id;
                          Depends    : out Dependency_Maps.Map)
   is
      Depends_Contract : constant Node_Id :=
        Get_Pragma (Subprogram, Pragma_Depends);
   begin
      Depends := Parse_Depends (Depends_Contract);
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
      if Gnat2Why_Args.Flow_Dump_Graphs then
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

   function Flow_Analyse_Entity (E : Entity_Id)
                                 return Flow_Analysis_Graphs
   is
      FA : Flow_Analysis_Graphs;
   begin
      case Ekind (E) is
         when Subprogram_Kind =>
            FA := Flow_Analysis_Graphs'
              (Kind             => E_Subprogram_Body,
               Analyzed_Entity  => E,
               Scope            => SPARK_Util.Get_Subprogram_Body (E),
               Start_Vertex     => Null_Vertex,
               End_Vertex       => Null_Vertex,
               CFG              => Create,
               DDG              => Create,
               CDG              => Create,
               TDG              => Create,
               PDG              => Create,
               All_Vars         => Flow_Id_Sets.Empty_Set,
               Loops            => Node_Sets.Empty_Set,
               Magic_Source     => Magic_String_To_Node_Sets.Empty_Map,
               Aliasing_Present => False,
               Base_Filename    => To_Unbounded_String ("subprogram_"),
               Is_Main          => Might_Be_Main (E),
               Is_Generative    => not (Present
                                          (Get_Pragma (E, Pragma_Global)) or
                                        Present
                                          (Get_Pragma (E, Pragma_Depends))));

         when E_Package =>
            FA := Flow_Analysis_Graphs'
              (Kind             => E_Package,
               Analyzed_Entity  => E,
               Scope            => Get_Enclosing_Scope (E),
               Start_Vertex     => Null_Vertex,
               End_Vertex       => Null_Vertex,
               CFG              => Create,
               DDG              => Create,
               CDG              => Create,
               TDG              => Create,
               PDG              => Create,
               All_Vars         => Flow_Id_Sets.Empty_Set,
               Loops            => Node_Sets.Empty_Set,
               Magic_Source     => Magic_String_To_Node_Sets.Empty_Map,
               Aliasing_Present => False,
               Base_Filename    =>  To_Unbounded_String ("package_spec_"));

         when E_Package_Body =>
            FA := Flow_Analysis_Graphs'
              (Kind             => E_Package_Body,
               Analyzed_Entity  => E,
               Scope            => Get_Enclosing_Body_Scope (E),
               Start_Vertex     => Null_Vertex,
               End_Vertex       => Null_Vertex,
               CFG              => Create,
               DDG              => Create,
               CDG              => Create,
               TDG              => Create,
               PDG              => Create,
               All_Vars         => Flow_Id_Sets.Empty_Set,
               Loops            => Node_Sets.Empty_Set,
               Magic_Source     => Magic_String_To_Node_Sets.Empty_Map,
               Aliasing_Present => False,
               Base_Filename    => To_Unbounded_String ("package_body_"));

         when others =>
            raise Why.Not_SPARK;
      end case;
      pragma Assert (Is_Valid (FA));

      Append (FA.Base_Filename, Get_Name_String (Chars (E)));

      if Gnat2Why_Args.Flow_Dump_Graphs then
         Write_Str (Character'Val (8#33#) & "[32m" &
                      "Flow analysis (cons) of " &
                      Entity_Kind'Image (FA.Kind) &
                      " " &
                      Character'Val (8#33#) & "[1m" &
                      Get_Name_String (Chars (E)) &
                      Character'Val (8#33#) & "[0m");
         Write_Eol;
      end if;

      FA.Magic_Source := Calculate_Magic_Mapping (FA.Scope);

      if Debug_Print_Magic_Source_Set then
         for C in FA.Magic_Source.Iterate loop
            Write_Str (Magic_String_To_Node_Sets.Key (C).all);
            Write_Eol;

            Indent;
            for E of Magic_String_To_Node_Sets.Element (C) loop
               Sprint_Node (E);
               Write_Eol;
            end loop;
            Outdent;
         end loop;
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

   procedure Flow_Analyse_CUnit is

      function Analysis_Requested (E : Entity_Id) return Boolean;
      --  Returns true if entity E has to be analyzed.

      procedure Create_Flow_Result_File
        (FA            : Flow_Analysis_Graphs_Root;
         Found_Error   : Boolean;
         Found_Warning : Boolean);
      --  If no errors/warnings were generated during flow analysis then
      --  we create a file that contains the word OK.

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

      function Analysis_Requested (E : Entity_Id) return Boolean
      is
         (Is_In_Analyzed_Files (E) and then Is_Requested_Subprogram (E));

      -----------------------------
      -- Create_Flow_Result_File --
      -----------------------------

      procedure Create_Flow_Result_File
        (FA            : Flow_Analysis_Graphs_Root;
         Found_Error   : Boolean;
         Found_Warning : Boolean)
      is
      begin
         if not Found_Error
           and then not Found_Warning
         then
            declare
               FD : Ada.Text_IO.File_Type;

               Filename : constant Unbounded_String :=
                 FA.Base_Filename & ".flow_ok";
            begin
               Ada.Text_IO.Create
                 (FD, Ada.Text_IO.Out_File, To_String (Filename));
               Ada.Text_IO.Put (FD, "OK");
               Ada.Text_IO.New_Line (FD);
               Ada.Text_IO.Close (FD);
            end;
         end if;
      end Create_Flow_Result_File;

      --------------------------
      -- Is_In_Analyzed_Files --
      --------------------------

      function Is_In_Analyzed_Files (E : Entity_Id) return Boolean
      is
      begin
         --  If we have an empty files list we analyze everything
         if Gnat2Why_Args.Analyze_File.Is_Empty then
            return True;
         end if;

         --  We strip everything from paths and extensions and then we
         --  check if we have a match.
         declare
            Basename        : constant String :=
              Get_Name_String (Reference_Name
                                 (Get_Source_File_Index (Sloc (E))));
            Basename_No_Ext : constant String :=
              Basename (Basename'First .. Basename'Last - 4);
         begin
            for A_File of Gnat2Why_Args.Analyze_File loop
               declare
                  Filename        : constant String := File_Name (A_File);
                  Filename_No_Ext : constant String :=
                    Filename (Filename'First .. Filename'Last - 4);
               begin
                  if Filename_No_Ext = Basename_No_Ext then
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

      function Is_Requested_Subprogram (E : Entity_Id) return Boolean
      is
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

      FA_Graphs     : Analysis_Maps.Map;
      Success       : Boolean;
      Found_Error   : Boolean;
      Found_Warning : Boolean;
   begin
      --  Process entities and construct graphs if necessary
      for E of All_Entities loop
         case Ekind (E) is
            when Subprogram_Kind =>
               if Analysis_Requested (E)
                 and Subprogram_Body_In_SPARK (E)
               then
                  FA_Graphs.Include (E, Flow_Analyse_Entity (E));
               end if;

            when E_Package =>
               declare
                  Pkg_Spec : constant Node_Id := Get_Enclosing_Scope (E);
                  Pkg_Body : Node_Id;
               begin
                  if Analysis_Requested (E)
                    and Entity_In_SPARK (E)
                    and not In_Predefined_Unit (E)
                  then
                     FA_Graphs.Include (E, Flow_Analyse_Entity (E));

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
                        pragma Assert (Nkind (Pkg_Body) = N_Defining_Identifier
                                         and then
                                         Ekind (Pkg_Body) = E_Package_Body);
                        FA_Graphs.Include (Pkg_Body,
                                           Flow_Analyse_Entity (Pkg_Body));
                     end if;
                  end if;
               end;

            when others =>
               null;
         end case;
      end loop;

      --  TODO: Perform interprocedural analysis

      --  Analyse graphs and produce error messages
      for FA of FA_Graphs loop
         Found_Error   := False;
         Found_Warning := False;

         if Gnat2Why_Args.Flow_Dump_Graphs then
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
            case FA.Kind is
               when E_Subprogram_Body =>
                  Analysis.Find_Unwritten_Exports (FA,
                                                   Found_Error,
                                                   Found_Warning);
                  Analysis.Find_Ineffective_Imports (FA,
                                                     Found_Error,
                                                     Found_Warning);
                  Analysis.Find_Illegal_Updates (FA,
                                                 Found_Error,
                                                 Found_Warning);
                  Analysis.Find_Ineffective_Statements (FA,
                                                        Found_Error,
                                                        Found_Warning);
                  Analysis.Find_Use_Of_Uninitialised_Variables (FA,
                                                                Found_Error,
                                                                Found_Warning);
                  Analysis.Find_Unused_Objects (FA,
                                                Found_Error,
                                                Found_Warning);
                  Analysis.Check_Contracts (FA,
                                            Found_Error,
                                            Found_Warning);
                  Analysis.Analyse_Main (FA,
                                         Found_Error,
                                         Found_Warning);

               when E_Package =>
                  --  !!! Issue here with detection of uninitialized
                  --  !!! state. Needs resolution of M628-002.
                  null;

               when E_Package_Body =>
                  Analysis.Find_Use_Of_Uninitialised_Variables (FA,
                                                                Found_Error,
                                                                Found_Warning);
                  Analysis.Find_Ineffective_Statements (FA,
                                                        Found_Error,
                                                        Found_Warning);
                  Analysis.Find_Illegal_Updates (FA,
                                                 Found_Error,
                                                 Found_Warning);
            end case;
         end if;

         Create_Flow_Result_File
           (FA,
            Found_Error,
            Found_Warning);

      end loop;

   end Flow_Analyse_CUnit;

end Flow;
