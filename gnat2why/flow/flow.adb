------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                                 F L O W                                  --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                  Copyright (C) 2013-2016, Altran UK Limited              --
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
with Ada.Strings.Maps;
with Ada.Strings;                    use Ada.Strings;
with Assumptions;                    use Assumptions;
with Errout;                         use Errout;
with Flow.Analysis;
with Flow.Control_Dependence_Graph;
with Flow.Control_Flow_Graph;
with Flow.Data_Dependence_Graph;
with Flow.Interprocedural;
with Flow.Program_Dependence_Graph;
with Flow.Slice;                     use Flow.Slice;
with Flow_Classwide;                 use Flow_Classwide;
with Flow_Debug;                     use Flow_Debug;
with Flow_Generated_Globals;         use Flow_Generated_Globals;
with Flow_Generated_Globals.Phase_1; use Flow_Generated_Globals.Phase_1;
with Flow_Generated_Globals.Phase_2; use Flow_Generated_Globals.Phase_2;
with Flow_Error_Messages;            use Flow_Error_Messages;
with Flow_Utility;                   use Flow_Utility;
with Gnat2Why.Assumptions;           use Gnat2Why.Assumptions;
with Gnat2Why_Args;
with Lib;                            use Lib;
with Namet;                          use Namet;
with Nlists;                         use Nlists;
with Osint;                          use Osint;
with Output;                         use Output;
with Sem_Aux;                        use Sem_Aux;
with Sem_Util;                       use Sem_Util;
with Sem_Ch7;                        use Sem_Ch7;
with Sinfo;                          use Sinfo;
with Snames;                         use Snames;
with SPARK_Definition;               use SPARK_Definition;
with SPARK_Frame_Conditions;         use SPARK_Frame_Conditions;
with SPARK_Util;                     use SPARK_Util;
with Sprint;                         use Sprint;
with VC_Kinds;                       use VC_Kinds;
with Why;

use type Ada.Containers.Count_Type;

package body Flow is

   --  These debug options control which graphs to output.

   Debug_Print_CFG           : constant Boolean := True;
   Debug_Print_Intermediates : constant Boolean := False;
   Debug_Print_PDG           : constant Boolean := True;

   --  These debug options control some of the tracing produced.

   Debug_Trace_Scoping : constant Boolean := True;

   ------------------------------------------------------------

   use Flow_Graphs;
   use Global_Info_Lists;
   use Name_Sets;

   Temp_String : Unbounded_String := Null_Unbounded_String;

   Whitespace : constant Ada.Strings.Maps.Character_Set :=
     Ada.Strings.Maps.To_Set
       (Ada.Characters.Latin_1.Space &
        Ada.Characters.Latin_1.CR &
        Ada.Characters.Latin_1.LF);

   procedure Add_To_Temp_String (S : String);
   --  Nasty nasty hack to add the given string to a global variable,
   --  Temp_String. We use this to pretty print nodes via Sprint_Node.

   function Flow_Analyse_Entity (E                  : Entity_Id;
                                 S                  : Entity_Id;
                                 Generating_Globals : Boolean)
                                 return Flow_Analysis_Graphs
   with Pre  => Ekind (E) in E_Function       |
                             E_Procedure      |
                             E_Task_Type      |
                             E_Protected_Type |
                             E_Entry          |
                             E_Package        |
                             E_Package_Body,
        Post => Is_Valid (Flow_Analyse_Entity'Result);
   --  Flow analyse the given entity E with a specification entity S (i.e.
   --  where the N_Contract node is attached). Do nothing for entities with
   --  no body or not in SPARK 2014.

   use type Analysis_Maps.Map;

   procedure Build_Graphs_For_Compilation_Unit
     (FA_Graphs               : out Analysis_Maps.Map;
      Routines_With_Spec_Only : out Global_Info_Lists.List;
      Generating_Globals      : Boolean)
   with Post => (if not Generating_Globals then
                   Routines_With_Spec_Only.Is_Empty);
   --  Build all flow graphs for the current compilation unit

   function Last_Statement_Is_Raise (E : Entity_Id) return Boolean
   with Pre => Ekind (E) in E_Entry | E_Function | E_Procedure | E_Task_Type;
   --  Returns True if the last statement in the
   --  Handled_Sequence_Of_Statements of E is an N_Raise_Statement.

   -------------------------
   -- Add_To_Temp_String  --
   -------------------------

   procedure Add_To_Temp_String (S : String) is
   begin
      Append
        (Temp_String,
         Trim (To_Unbounded_String (S), Whitespace, Whitespace));
   end Add_To_Temp_String;

   ----------------------
   -- Vertex_Pair_Hash --
   ----------------------

   function Vertex_Pair_Hash
     (VD : Vertex_Pair)
      return Ada.Containers.Hash_Type is
      use Ada.Containers;
   begin
      return Flow_Graphs.Vertex_Hash (VD.To) +
             Flow_Graphs.Vertex_Hash (VD.From);
   end Vertex_Pair_Hash;

   ------------------------
   -- Print_Graph_Vertex --
   ------------------------

   procedure Print_Graph_Vertex (G : Flow_Graphs.Graph;
                                 M : Attribute_Maps.Map;
                                 V : Flow_Graphs.Vertex_Id)
   is
      F : constant Flow_Id := G.Get_Key (V);
      A : V_Attributes renames M (V);

      procedure Format_Item (K, V : String);

      function Flow_Id_Image (F : Flow_Id) return String;

      -----------------
      -- Format_Item --
      -----------------

      procedure Format_Item (K, V : String) is
      begin
         Write_Line (K & ": " & V);
      end Format_Item;

      -------------------
      -- Flow_Id_Image --
      -------------------

      function Flow_Id_Image (F : Flow_Id) return String is
        ((case F.Kind is
             when Direct_Mapping =>
                (if Nkind (Get_Direct_Mapping_Id (F)) in N_Entity
                 then Flow_Id_To_String (F)
                 else Node_Or_Entity_Id'Image (Get_Direct_Mapping_Id (F))),
             when others =>
                Flow_Id_To_String (F)) & "|" & F.Variant'Img);

   --  Start of processing for Print_Graph_Vertex

   begin
      Write_Line ("Graph vertex [" &
                    Natural'Image (G.Vertex_To_Natural (V)) &
                    "] (" &
                    Flow_Id_Image (F) &
                    "):");

      Indent;

      Format_Item ("Is_Null_Node", Boolean'Image (A.Is_Null_Node));
      Format_Item ("Is_Exceptional_Branch",
                   Boolean'Image (A.Is_Exceptional_Branch));
      Format_Item ("Is_Exceptional_Path",
                   Boolean'Image (A.Is_Exceptional_Path));
      Format_Item ("Is_Program_Node", Boolean'Image (A.Is_Program_Node));
      Format_Item ("Is_Proof", Boolean'Image (A.Is_Proof));
      Format_Item ("Is_Precondition", Boolean'Image (A.Is_Precondition));
      Format_Item ("Is_Default_Init", Boolean'Image (A.Is_Default_Init));
      Format_Item ("Is_Loop_Entry", Boolean'Image (A.Is_Loop_Entry));
      Format_Item ("Is_Initialized", Boolean'Image (A.Is_Initialized));
      Format_Item ("Is_Function_Return", Boolean'Image (A.Is_Function_Return));
      Format_Item ("Is_Global", Boolean'Image (A.Is_Global));
      Format_Item ("Is_Loop_Parameter", Boolean'Image (A.Is_Loop_Parameter));
      Format_Item ("Is_Import", Boolean'Image (A.Is_Import));
      Format_Item ("Is_Export", Boolean'Image (A.Is_Export));
      Format_Item ("Mode", Param_Mode'Image (A.Mode));
      Format_Item ("Is_Package_State", Boolean'Image (A.Is_Package_State));
      Format_Item ("Is_Constant", Boolean'Image (A.Is_Constant));
      Format_Item ("Is_Callsite", Boolean'Image (A.Is_Callsite));
      Format_Item ("Is_Parameter", Boolean'Image (A.Is_Parameter));
      Format_Item ("Is_Discr_Or_Bounds_Parameter",
                   Boolean'Image (A.Is_Discr_Or_Bounds_Parameter));
      Format_Item ("Is_Global_Parameter",
                   Boolean'Image (A.Is_Global_Parameter));
      Format_Item ("Execution", Execution_Kind_T'Image (A.Execution));
      Format_Item ("Perform_IPFA", Boolean'Image (A.Perform_IPFA));

      Format_Item ("Call_Vertex", Flow_Id_Image (A.Call_Vertex));

      if A.Is_Parameter then
         Format_Item ("Parameter_Actual", Flow_Id_Image (A.Parameter_Actual));
      end if;
      if A.Is_Parameter or A.Is_Global_Parameter then
         Format_Item ("Parameter_Formal", Flow_Id_Image (A.Parameter_Actual));
      end if;

      Write_Str ("Variables_Defined: ");
      Print_Node_Set (A.Variables_Defined);

      Write_Str ("Variables_Used: ");
      Print_Node_Set (A.Variables_Used);

      Write_Str ("Subprograms_Called: ");
      Print_Node_Set (A.Subprograms_Called);

      Write_Str ("Variables_Explicitly_Used: ");
      Print_Node_Set (A.Variables_Explicitly_Used);

      Outdent;
   end Print_Graph_Vertex;

   --------------
   -- Is_Valid --
   --------------

   function Is_Valid (X : Flow_Analysis_Graphs_Root)
                      return Boolean
   is ((case X.Kind is
        when Kind_Subprogram =>
           Is_Subprogram (X.Analyzed_Entity),
        when Kind_Task =>
           Ekind (X.Analyzed_Entity) = E_Task_Type,
        when Kind_Entry =>
           Ekind (X.Analyzed_Entity) = E_Entry,
        when Kind_Package =>
           Ekind (X.Analyzed_Entity) = E_Package,
        when Kind_Package_Body =>
           Ekind (X.Analyzed_Entity) = E_Package_Body)
       and then (if not X.Generating_Globals
                 then not X.GG.Aborted and X.GG.Globals.Is_Empty)
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
      if No (N) then
         return Empty;
      end if;
      pragma Assert (Nkind (N) = N_Iteration_Scheme);

      N := Loop_Parameter_Specification (N);
      if No (N) then
         return Empty;
      end if;
      pragma Assert (Nkind (N) = N_Loop_Parameter_Specification);

      return Defining_Identifier (N);
   end Loop_Parameter_From_Loop;

   -----------------
   -- Print_Graph --
   -----------------

   procedure Print_Graph
     (Filename          : String;
      Analyzed_Entity   : Entity_Id;
      G                 : Graph;
      M                 : Attribute_Maps.Map;
      Start_Vertex      : Vertex_Id := Null_Vertex;
      Helper_End_Vertex : Vertex_Id := Null_Vertex;
      End_Vertex        : Vertex_Id := Null_Vertex) is

      function NDI
        (G : Graph;
         V : Vertex_Id) return Node_Display_Info;
      --  Pretty-printing for each vertex in the dot output.

      function EDI
        (G      : Graph;
         A      : Vertex_Id;
         B      : Vertex_Id;
         Marked : Boolean;
         Colour : Edge_Colours) return Edge_Display_Info;
      --  Pretty-printing for each edge in the dot output.

      ---------
      -- NDI --
      ---------

      function NDI
        (G : Graph;
         V : Vertex_Id) return Node_Display_Info
      is
         Rv : Node_Display_Info := Node_Display_Info'
           (Show        => True,
            Shape       => Node_Shape_T'First,
            Colour      => Null_Unbounded_String,
            Fill_Colour => Null_Unbounded_String,
            Label       => Null_Unbounded_String);

         F : Flow_Id      renames G.Get_Key (V);
         A : V_Attributes renames M (V);

         NBSP : constant String := "&nbsp;";
         --  HTML tag for non-breaking space

         procedure Print_Node (N : Node_Id);

         ----------------
         -- Print_Node --
         ----------------

         procedure Print_Node (N : Node_Id) is
         begin
            if Comes_From_Source (N) then
               po (Union_Id (N));
            else
               pg (Union_Id (N));
            end if;
         end Print_Node;

      --  Start of processing for NDI

      begin
         Temp_String := Null_Unbounded_String;
         Set_Special_Output (Add_To_Temp_String'Access);

         if A.Is_Exceptional_Path then
            Rv.Fill_Colour := To_Unbounded_String ("gold");
         end if;

         if A.Is_Null_Node then
            Rv.Show := False;

         elsif V = Start_Vertex then
            Write_Str ("start");
            Rv.Shape := Shape_None;
            Rv.Show  := G.In_Neighbour_Count (V) > 0 or else
              G.Out_Neighbour_Count (V) > 0;

         elsif V = Helper_End_Vertex then
            Write_Str ("helper end");
            Rv.Shape := Shape_None;
            Rv.Show  := G.In_Neighbour_Count (V) > 0 or else
              G.Out_Neighbour_Count (V) > 0;

         elsif V = End_Vertex then
            Write_Str ("end");
            Rv.Shape := Shape_None;
            Rv.Show  := G.In_Neighbour_Count (V) > 0 or else
              G.Out_Neighbour_Count (V) > 0;

         elsif F.Kind = Synthetic_Null_Export then
            case F.Variant is
               when Initial_Value =>
                  Rv.Show := False;

               when Final_Value =>
                  Rv.Colour := To_Unbounded_String ("chartreuse");
                  Rv.Shape  := Shape_None;
                  Write_Str ("null");

               when others =>
                  raise Program_Error;
            end case;

         elsif A.Pretty_Print_Kind = Pretty_Print_Folded_Function_Check then
            Write_Str ("ff check for: ");
            Print_Node (A.Error_Location);

         elsif A.Pretty_Print_Kind = Pretty_Print_Loop_Init then
            Write_Str ("initialization in loop ");
            Print_Node (A.Error_Location);

         elsif A.Pretty_Print_Kind = Pretty_Print_DIC then
            Rv.Shape := Shape_None;
            Write_Str ("Default Initial Condition: ");
            Print_Node (A.Error_Location);

         elsif A.Pretty_Print_Kind = Pretty_Print_Record_Field then
            --  Sanity check that we only have one defined variable
            pragma Assert (A.Variables_Defined.Length = 1);

            declare
               Var_Def : Flow_Id;
            begin
               Var_Def := A.Variables_Defined (A.Variables_Defined.First);

               Write_Str (Flow_Id_To_String (Var_Def));
               Write_Str (" => ");
            end;

            declare
               Commas_Remaining : Integer :=
                 Integer (A.Variables_Explicitly_Used.Length) - 1;
            begin
               if Commas_Remaining < 0 then
                  Write_Str ("null");
               end if;

               for Var_Used of A.Variables_Explicitly_Used loop
                  Write_Str (Flow_Id_To_String (Var_Used));

                  if Commas_Remaining > 0 then
                     Write_Str (", ");
                  end if;

                  Commas_Remaining := Commas_Remaining - 1;
               end loop;
            end;

         elsif A.Pretty_Print_Kind = Pretty_Print_Entry_Barrier then
            Rv.Shape := Shape_Diamond;
            Write_Str ("when ");
            Print_Node (Get_Direct_Mapping_Id (F));

         elsif A.Pretty_Print_Kind /= Pretty_Print_Null then
            raise Program_Error;

         elsif A.Is_Parameter then
            Rv.Shape := Shape_None;

            case F.Variant is
               when In_View =>
                  pragma Assert (A.Parameter_Formal.Kind = Direct_Mapping);
                  pragma Assert (A.Parameter_Actual.Kind = Direct_Mapping);
                  Print_Node (Get_Direct_Mapping_Id (A.Parameter_Formal));
                  Write_Str ("'in");
                  Write_Str (NBSP & ":=" & NBSP);
                  Print_Node (Get_Direct_Mapping_Id (A.Parameter_Actual));
                  if A.Is_Discr_Or_Bounds_Parameter then
                     Write_Str ("'discr_or_bounds");
                  end if;

               when Out_View =>
                  pragma Assert (A.Parameter_Formal.Kind = Direct_Mapping);
                  pragma Assert (A.Parameter_Actual.Kind = Direct_Mapping);
                  pragma Assert (not A.Is_Discr_Or_Bounds_Parameter);
                  Print_Node (Get_Direct_Mapping_Id (A.Parameter_Actual));
                  Write_Str (NBSP & ":=" & NBSP);
                  Print_Node (Get_Direct_Mapping_Id (A.Parameter_Formal));
                  Write_Str ("'out");

               when others =>
                  raise Program_Error;
            end case;

         elsif A.Is_Global_Parameter then
            Rv.Shape := Shape_None;

            Write_Str ("global" & NBSP);
            Sprint_Flow_Id (A.Parameter_Formal);
            case A.Parameter_Formal.Variant is
               when In_View =>
                  if A.Is_Discr_Or_Bounds_Parameter then
                     Write_Str ("'discr_or_bounds");
                  end if;
                  Write_Str ("'in");

               when Out_View =>
                  pragma Assert (not A.Is_Discr_Or_Bounds_Parameter);
                  Write_Str ("'out");

               when others =>
                  raise Program_Error;
            end case;

         elsif A.Is_Implicit_Parameter then
            Rv.Shape := Shape_None;

            Write_Str ("implicit" & NBSP);
            Sprint_Flow_Id (A.Parameter_Formal);
            case A.Parameter_Formal.Variant is
               when In_View =>
                  Write_Str ("'in");

               when Out_View =>
                  Write_Str ("'out");

               when others =>
                  raise Program_Error;
            end case;

         elsif A.Is_Default_Init then
            Rv.Shape := Shape_None;

            Sprint_Flow_Id (A.Default_Init_Var);
            if Present (A.Default_Init_Val) then
               Write_Str (NBSP & "is by default" & NBSP);
               Print_Node (A.Default_Init_Val);
            else
               Write_Str (NBSP & "is initialized implicitly");
            end if;

         elsif A.Is_Package_Initialization then
            Rv.Shape := Shape_None;
            Write_Str ("initializes ");

            pragma Assert (F.Kind = Direct_Mapping);
            declare
               N : constant Node_Id := Get_Direct_Mapping_Id (F);
            begin
               --  Look at the postcondition of Find_Node in
               --  Do_Package_Body_Or_Stub in CFG as to why only these
               --  four need to be supported.
               case Nkind (N) is
                  when N_Component_Association =>
                     Sprint_Comma_List (Choices (N));
                     Write_Str (" from ");
                     Print_Node (Expression (N));
                  when N_Defining_Identifier |
                       N_Identifier          |
                       N_Expanded_Name       =>
                     Print_Node (N);
                  when others =>
                     raise Why.Unexpected_Node;
               end case;
            end;

         else
            if A.Is_Precondition then
               Rv.Shape := Shape_None;
               Write_Str ("precondition ");
            elsif A.Is_Postcondition then
               Rv.Shape := Shape_None;
               Write_Str ("postcondition ");
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
                           Print_Node (Expression (N));

                        when N_Case_Statement_Alternative =>
                           Rv.Shape := Shape_None;
                           Write_Str ("when ");
                           Sprint_Comma_List (Discrete_Choices (N));

                        when N_Defining_Identifier =>
                           case Ekind (N) is
                              when E_Return_Statement =>
                                 Write_Str ("return ");
                                 Print_Node (A.Aux_Node);

                              when others =>
                                 Sprint_Flow_Id (F);
                           end case;

                        when N_Elsif_Part =>
                           Rv.Shape := Shape_Diamond;
                           Write_Str ("elsif ");
                           Print_Node (Condition (N));

                        when N_If_Statement =>
                           Rv.Shape := Shape_Diamond;
                           Write_Str ("if ");
                           Print_Node (Condition (N));

                        when N_Loop_Statement =>
                           Rv.Shape := Shape_Diamond;
                           if No (Iteration_Scheme (N)) then
                              --  Basic loop. Should never
                              --  appear as a vertex in the
                              --  graph.
                              pragma Assert (False);
                           elsif Present
                             (Condition (Iteration_Scheme (N)))
                           then
                              --  While loop.
                              Write_Str ("while ");
                              Print_Node (Condition (Iteration_Scheme (N)));
                           else
                              Print_Node (Iteration_Scheme (N));
                           end if;

                        when N_Procedure_Call_Statement =>
                           Rv.Shape := Shape_Box;
                           Write_Str ("call ");
                           Print_Node (Name (N));

                        when N_Null_Statement =>
                           --  This is here in order NOT to print an empty
                           --  bubble. Sprint usually, but not always,
                           --  returns "null;" for this node.
                           Write_Str ("null;");

                        when N_Entry_Body_Formal_Part =>
                           Rv.Shape := Shape_None;
                           Write_Str ("barrier");

                        when others =>
                           Print_Node (N);
                     end case;
                  end;

               when Record_Field | Magic_String =>
                  Sprint_Flow_Id (F);

               when Synthetic_Null_Export | Null_Value =>
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

                  declare
                     S : constant Flow_Scope :=
                       (if F.Kind in Direct_Mapping | Record_Field
                        then Get_Flow_Scope (Analyzed_Entity)
                        else Null_Flow_Scope);
                  begin
                     if Is_Volatile (F, S) then
                        Write_Str ("\nvolatile:");
                        if Has_Async_Readers (F, S) then
                           Write_Str (NBSP & "AR");
                        end if;
                        if Has_Async_Writers (F, S) then
                           Write_Str (NBSP & "AW");
                        end if;
                        if Has_Effective_Reads (F, S) then
                           Write_Str (NBSP & "ER");
                        end if;
                        if Has_Effective_Writes (F, S) then
                           Write_Str (NBSP & "EW");
                        end if;
                     end if;
                  end;

                  if not A.Is_Initialized then
                     Rv.Colour := To_Unbounded_String ("red");
                  elsif Is_Discriminant (F) or Is_Record_Tag (F) then
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

            if not A.Loops.Is_Empty and not (A.Is_Parameter or
                                             A.Is_Global_Parameter)
            then
               Write_Str ("\nLoops:");
               for Loop_Identifier of A.Loops loop
                  Write_Str (NBSP);
                  Print_Node (Loop_Identifier);
               end loop;
            end if;

            if A.Perform_IPFA then
               Write_Str ("\nIPFA");
            end if;

            if A.Is_Global then
               Write_Str ("\n(global)");
            end if;
         end if;

         if not A.Variables_Used.Is_Empty then
            Write_Str ("\nVU: {");
            declare
               First : Boolean := True;
            begin
               for F of A.Variables_Used loop
                  if First then
                     First := False;
                  else
                     Write_Str (", ");
                  end if;
                  Sprint_Flow_Id (F);
               end loop;
            end;
            Write_Str ("}");
         end if;

         if not A.Subprograms_Called.Is_Empty then
            Write_Str ("\nSC: {");
            declare
               First : Boolean := True;
            begin
               for E of A.Subprograms_Called loop
                  if First then
                     First := False;
                  else
                     Write_Str (", ");
                  end if;
                  Sprint_Flow_Id (Direct_Mapping_Id (E));
               end loop;
            end;
            Write_Str ("}");
         end if;

         if not A.Variables_Defined.Is_Empty then
            Write_Str ("\nVD: {");
            declare
               First : Boolean := True;
            begin
               for F of A.Variables_Defined loop
                  if First then
                     First := False;
                  else
                     Write_Str (", ");
                  end if;
                  Sprint_Flow_Id (F);
               end loop;
            end;
            Write_Str ("}");
         end if;

         case A.Execution is
            when Normal_Execution =>
               null;
            when Barrier =>
               Write_Str ("\nExecution: BARRIER");
            when Abnormal_Termination =>
               Write_Str ("\nExecution: ABEND");
            when Infinite_Loop =>
               Write_Str ("\nExecution: INF");
         end case;

         if A.Is_Exceptional_Branch then
            Write_Str ("\nExceptional_Branch");
         end if;

         if A.Is_Proof then
            Write_Str ("\nPROOF");
         end if;

         Write_Str ("\n<VId:" & Natural'Image (G.Vertex_To_Natural (V)) & ">");

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
        (G      : Graph;
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

            when EC_Barrier =>
               Rv.Colour := To_Unbounded_String ("gold");
               Rv.Label  := To_Unbounded_String ("barrier");

            when EC_Abend =>
               --  Using the same colour as for barriers, since this one
               --  won't ever show up normally (we prune all such paths).
               --  But in some debug modes you can see it, and they are
               --  reasonably similar...
               Rv.Colour := To_Unbounded_String ("gold");
               Rv.Label  := To_Unbounded_String ("abend");

            when EC_Inf =>
               Rv.Colour := To_Unbounded_String ("chartreuse"); --  Hi Martin!
               Rv.Label  := To_Unbounded_String ("inf");

            when EC_DDG =>
               Rv.Colour := To_Unbounded_String ("red");

            when EC_TDG =>
               Rv.Colour := To_Unbounded_String ("cornflowerblue");
         end case;
         return Rv;
      end EDI;

   --  Start of processing for Print_Graph

   begin
      if Gnat2Why_Args.Debug_Mode then
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

   function Flow_Analyse_Entity (E                  : Entity_Id;
                                 S                  : Entity_Id;
                                 Generating_Globals : Boolean)
                                 return Flow_Analysis_Graphs
   is
      procedure Debug (Str : String);
      --  Write debug string

      procedure Debug (Str : String; V : Boolean);
      --  Write debug string followed by yes or no, depending on V

      -----------------
      -- Debug --
      -----------------

      procedure Debug (Str : String) is
      begin
         if Gnat2Why_Args.Flow_Advanced_Debug then
            Write_Line (Str);
         end if;
      end Debug;

      procedure Debug (Str : String; V : Boolean) is
      begin
         Debug (Str & (if V then "yes" else "no"));
      end Debug;

      FA : Flow_Analysis_Graphs_Root
        (Kind               => (case Ekind (E) is
                                when E_Function
                                   | E_Procedure     => Kind_Subprogram,
                                when E_Task_Type     => Kind_Task,
                                when E_Entry         => Kind_Entry,
                                when E_Package       => Kind_Package,
                                when E_Package_Body  => Kind_Package_Body,
                                when others          => raise Program_Error),
         Generating_Globals => Generating_Globals);

      Phase : constant String := (if Generating_Globals
                                  then "Global generation"
                                  else "Flow analysis");

   --  Start of processing for Flow_Analyse_Entity

   begin
      FA.Analyzed_Entity       := E;
      FA.Spec_Entity           := S;
      FA.Start_Vertex          := Null_Vertex;
      FA.Helper_End_Vertex     := Null_Vertex;
      FA.End_Vertex            := Null_Vertex;
      FA.CFG                   := Create;
      FA.DDG                   := Create;
      FA.CDG                   := Create;
      FA.TDG                   := Create;
      FA.PDG                   := Create;
      FA.Atr                   := Attribute_Maps.Empty_Map;
      FA.Other_Fields          := Vertex_To_Vertex_Set_Maps.Empty_Map;
      FA.Local_Constants       := Node_Sets.Empty_Set;
      FA.All_Vars              := Flow_Id_Sets.Empty_Set;
      FA.Unmodified_Vars       := Node_Sets.Empty_Set;
      FA.Unreferenced_Vars     := Node_Sets.Empty_Set;
      FA.Loops                 := Node_Sets.Empty_Set;
      FA.Dependency_Map        := Dependency_Maps.Empty_Map;
      FA.No_Errors_Or_Warnings := True;
      FA.Direct_Calls          := Node_Sets.Empty_Set;
      FA.Tasking               := (others => Node_Sets.Empty_Set);

      --  Generate Globals (gg) or Flow Analysis (fa)
      FA.Base_Filename := To_Unbounded_String (if Generating_Globals
                                               then "gg_"
                                               else "fa_");

      case Ekind (E) is
         when E_Entry     |
              E_Task_Type |
              E_Function  |
              E_Procedure =>
            FA.B_Scope := Get_Flow_Scope (Get_Body (E));
            FA.S_Scope := Get_Flow_Scope (E);

            Append (FA.Base_Filename, "subprogram_");

            FA.Is_Main :=
              (case Ekind (E) is
               when E_Function
                  | E_Procedure => Might_Be_Main (E),
               when E_Entry     => False,
               when E_Task_Type => True,
               when others      => raise Program_Error);

            FA.Last_Statement_Is_Raise := Last_Statement_Is_Raise (E);

            FA.Depends_N := Get_Pragma (E, Pragma_Depends);
            FA.Global_N  := Get_Pragma (E, Pragma_Global);

            declare
               Body_E : constant Entity_Id := Get_Body_Entity (E);
            begin
               FA.Refined_Depends_N := Get_Pragma (Body_E,
                                                   Pragma_Refined_Depends);
               FA.Refined_Global_N  := Get_Pragma (Body_E,
                                                   Pragma_Refined_Global);
            end;

            FA.Is_Generative := Refinement_Needed (E);

            FA.No_Effects := False;
            if Ekind (E) = E_Function then
               FA.Function_Side_Effects_Present := False;
            end if;

         when E_Package =>
            FA.B_Scope       := Flow_Scope'(E, Private_Part);
            FA.S_Scope       := Flow_Scope'(E, Private_Part);

            Append (FA.Base_Filename, "pkg_spec_");

            FA.Initializes_N := Get_Pragma (E, Pragma_Initializes);

            FA.Visible_Vars  := Flow_Id_Sets.Empty_Set;
            FA.Spec_Vars     := Flow_Id_Sets.Empty_Set;

            FA.Is_Generative := No (FA.Initializes_N);

         when E_Package_Body =>
            FA.B_Scope       := Flow_Scope'(Spec_Entity (E), Body_Part);
            FA.S_Scope       := Flow_Scope'(Spec_Entity (E), Private_Part);

            Append (FA.Base_Filename, "pkg_body_");

            FA.Initializes_N := Get_Pragma (Spec_Entity (E),
                                            Pragma_Initializes);

            FA.Visible_Vars  := Flow_Id_Sets.Empty_Set;
            FA.Spec_Vars     := Flow_Id_Sets.Empty_Set;

            FA.Is_Generative := No (FA.Initializes_N);

         when others =>
            raise Program_Error;
      end case;

      FA.GG.Aborted := False;
      FA.GG.Globals := Node_Sets.Empty_Set;

      Append (FA.Base_Filename, Unique_Name (E));

      if Gnat2Why_Args.Flow_Advanced_Debug then
         Write_Line (Character'Val (8#33#) & "[32m" &
                     Phase & " (cons) of " &
                     FA.Kind'Img &
                     " " &
                     Character'Val (8#33#) & "[1m" &
                     Get_Name_String (Chars (E)) &
                     Character'Val (8#33#) & "[0m");

         Indent;

         if Debug_Trace_Scoping and not FA.Generating_Globals then
            Write_Str ("Spec_Scope: ");
            Print_Flow_Scope (FA.S_Scope);
            Write_Eol;
            declare
               Ptr : Flow_Scope := FA.S_Scope;
            begin
               Indent;
               while Ptr /= Null_Flow_Scope loop
                  case Valid_Section_T'(Ptr.Section) is
                     when Body_Part =>
                        Ptr.Section := Private_Part;

                     when Private_Part | Spec_Part =>
                        Ptr := Get_Enclosing_Flow_Scope (Ptr);
                  end case;
                  if Ptr /= Null_Flow_Scope then
                     Print_Flow_Scope (Ptr);
                     Write_Eol;
                  end if;
               end loop;
               Outdent;
            end;

            Write_Str ("Body_Scope: ");
            Print_Flow_Scope (FA.B_Scope);
            Write_Eol;
         end if;
      end if;

      if FA.Generating_Globals then
         --  If we already have all the needed contracts then we set Aborted
         --  flag and do not produce graphs.
         case FA.Kind is
            when Kind_Subprogram | Kind_Task | Kind_Entry =>
               if not FA.Is_Generative then
                  Debug ("skipped" & (if Present (FA.Global_N)
                                      then "(global found)"
                                      elsif Present (FA.Depends_N)
                                      then "(depends found)"
                                      else raise Program_Error));

                  --  Even if aborting we still collect tasking-related info
                  --  using control flow traversal and register the results.
                  Control_Flow_Graph.Create (FA);

                  GG_Register_Tasking_Info
                     (To_Entity_Name (FA.Analyzed_Entity),
                      FA.Tasking);

                  FA.GG.Aborted := True;
               end if;

               Debug ("Spec in SPARK: ", Entity_In_SPARK (E));
               Debug ("Body in SPARK: ", Entity_Body_In_SPARK (E));

            when Kind_Package =>
               if Present (FA.Initializes_N) then
                  --  There is no need to create a GG graph if the package has
                  --  an Initializes aspect.
                  Debug ("skipped (package spec)");

                  FA.GG.Aborted := True;
               else
                  Debug ("Spec in SPARK: ", Entity_Spec_In_SPARK (E));

                  --  We cannot create a GG graph if the spec is not in SPARK
                  if not Entity_Spec_In_SPARK (E) then
                     FA.GG.Aborted := True;
                  end if;
               end if;

            when Kind_Package_Body =>
               if Present (FA.Initializes_N) then
                  --  There is no need to create a GG graph if the package has
                  --  an Initializes aspect.

                  Debug ("skipped (package spec)");
                  Debug ("skipped (package body)");

                  FA.GG.Aborted := True;
               else
                  Debug ("Spec in SPARK: ",
                         Entity_Spec_In_SPARK (FA.Spec_Entity));
                  Debug ("Body in SPARK: ",
                         Entity_Body_In_SPARK (FA.Spec_Entity));

                  if not Entity_Body_In_SPARK (FA.Spec_Entity) then
                     FA.GG.Aborted := True;
                  end if;
               end if;

               declare
                  Refined_State_N : constant Node_Id :=
                    Get_Pragma (E, Pragma_Refined_State);

                  DM : Dependency_Maps.Map;
               begin
                  if Present (Refined_State_N) then
                     Debug ("Refinement found: yes");

                     DM := Parse_Refined_State (Refined_State_N);
                     if Gnat2Why_Args.Flow_Advanced_Debug then
                        for State in DM.Iterate loop
                           Write_Line ("State       :");
                           Indent;
                           Print_Flow_Id (Dependency_Maps.Key (State));
                           Outdent;
                           Write_Line ("Constituents:");
                           Indent;
                           for Constituent of DM (State) loop
                              Print_Flow_Id (Constituent);
                           end loop;
                           Outdent;
                        end loop;
                     end if;
                  else
                     Debug ("Refinement found: no");
                  end if;
               end;
         end case;

         if FA.GG.Aborted then
            if Gnat2Why_Args.Flow_Advanced_Debug then
               Outdent;
            end if;
            return FA;
         end if;
      end if;

      Control_Flow_Graph.Create (FA);

      --  Register tasking-related information; ignore packages because they
      --  are elaborated sequentially anyway.
      if FA.Generating_Globals
        and then FA.Kind in Kind_Subprogram |
                            Kind_Entry      |
                            Kind_Task
      then
         GG_Register_Tasking_Info (To_Entity_Name (FA.Analyzed_Entity),
                                   FA.Tasking);
      end if;

      if Gnat2Why_Args.Flow_Advanced_Debug then
         for Kind in Tasking_Info_Kind loop
            if not FA.Tasking (Kind).Is_Empty then
               Write_Str (Kind'Img & ": ");
               Print_Node_Set (FA.Tasking (Kind));
            end if;
         end loop;
      end if;

      --  Print this graph now in case the other algorithms barf
      if Debug_Print_CFG then
         Print_Graph (Filename          =>
                        To_String (FA.Base_Filename) & "_cfg",
                      Analyzed_Entity   => FA.Analyzed_Entity,
                      G                 => FA.CFG,
                      M                 => FA.Atr,
                      Start_Vertex      => FA.Start_Vertex,
                      Helper_End_Vertex => FA.Helper_End_Vertex,
                      End_Vertex        => FA.End_Vertex);
      end if;

      Control_Dependence_Graph.Create (FA);

      if Debug_Print_Intermediates then
         Print_Graph (Filename          =>
                        To_String (FA.Base_Filename) & "_cdg",
                      Analyzed_Entity   => FA.Analyzed_Entity,
                      G                 => FA.CDG,
                      M                 => FA.Atr,
                      Start_Vertex      => FA.Start_Vertex,
                      Helper_End_Vertex => FA.Helper_End_Vertex,
                      End_Vertex        => FA.End_Vertex);
      end if;

      Data_Dependence_Graph.Create (FA);
      Interprocedural.Create (FA);
      Program_Dependence_Graph.Create (FA);

      if Debug_Print_Intermediates then
         Print_Graph (Filename          =>
                        To_String (FA.Base_Filename) & "_ddg",
                      Analyzed_Entity   => FA.Analyzed_Entity,
                      G                 => FA.DDG,
                      M                 => FA.Atr,
                      Start_Vertex      => FA.Start_Vertex,
                      Helper_End_Vertex => FA.Helper_End_Vertex,
                      End_Vertex        => FA.End_Vertex);
      end if;

      if Debug_Print_PDG then
         Print_Graph (Filename          =>
                        To_String (FA.Base_Filename) & "_pdg",
                      Analyzed_Entity   => FA.Analyzed_Entity,
                      G                 => FA.PDG,
                      M                 => FA.Atr,
                      Start_Vertex      => FA.Start_Vertex,
                      Helper_End_Vertex => FA.Helper_End_Vertex,
                      End_Vertex        => FA.End_Vertex);
      end if;

      if Gnat2Why_Args.Flow_Advanced_Debug then
         Outdent;
      end if;

      return FA;

   end Flow_Analyse_Entity;

   ---------------------------------------
   -- Build_Graphs_For_Compilation_Unit --
   ---------------------------------------

   procedure Build_Graphs_For_Compilation_Unit
     (FA_Graphs               : out Analysis_Maps.Map;
      Routines_With_Spec_Only : out Global_Info_Lists.List;
      Generating_Globals      : Boolean)
   is

      procedure Build_Graphs_For_Entity (E : Entity_Id);
      --  Build graphs and, if requisted, collect globals for a given entity

      -----------------------------
      -- Build_Graphs_For_Entity --
      -----------------------------

      procedure Build_Graphs_For_Entity (E : Entity_Id) is
      begin
         case Ekind (E) is
            when E_Entry | E_Function | E_Procedure | E_Task_Type =>

               if SPARK_Util.Analysis_Requested (E, With_Inlined => True) then

                  --  Check for potentially blocking statements in callable
                  --  entities, i.e. entries and subprograms.
                  --  ??? also analyze spec

                  if Generating_Globals
                     and then Ekind (E) in E_Entry | E_Function | E_Procedure
                     and then Entity_Body_In_SPARK (E)
                  then
                     declare
                        Body_N : constant Node_Id := Get_Body (E);
                     begin
                        if Present (Body_N)
                          and then Has_Only_Nonblocking_Statements (Body_N)
                        then
                           GG_Register_Nonblocking (To_Entity_Name (E));
                        end if;
                     end;
                  end if;

                  if Entity_Body_In_SPARK (E) then
                     --  Body is in SPARK, so we just analyze it
                     FA_Graphs.Include (E, Flow_Analyse_Entity
                                          (E,
                                           E,
                                           Generating_Globals));
                  elsif Generating_Globals then
                     declare
                        Scope        : constant Flow_Scope :=
                          Get_Flow_Scope (E);
                        Global_Node  : constant Node_Id :=
                          Get_Contract_Node (E, Scope, Global_Contract);
                        Depends_Node : constant Node_Id :=
                          Get_Contract_Node (E, Scope, Depends_Contract);

                        Global_Info : Global_Phase_1_Info;
                     begin
                        if Present (Global_Node)
                          or else Present (Depends_Node)
                        then
                           --  If we have a user-provided Global or Depends
                           --  contract then we use Get_Globals to get that.
                           --  Note that in such a case components *_Calls
                           --  and Local_* will be left as empty sets.
                           declare
                              Proof_Ins : Flow_Id_Sets.Set;
                              Reads     : Flow_Id_Sets.Set;
                              Writes    : Flow_Id_Sets.Set;
                           begin
                              Get_Globals (Subprogram           => E,
                                           Scope                => Scope,
                                           Classwide            => False,
                                           Proof_Ins            => Proof_Ins,
                                           Reads                => Reads,
                                           Writes               => Writes,
                                           Use_Computed_Globals => False);

                              Global_Info := Global_Phase_1_Info'
                                (Name                  => To_Entity_Name (E),
                                 Kind                  =>
                                   (case Ekind (E) is
                                    when E_Entry     => Kind_Entry,
                                    when E_Function
                                       | E_Procedure => Kind_Subprogram,
                                    when E_Task_Type => Kind_Task,
                                    when others      => raise Program_Error),
                                 Origin                => Origin_User,
                                 Inputs_Proof          =>
                                   To_Name_Set (Proof_Ins),
                                 Inputs                => To_Name_Set (Reads),
                                 Outputs               => To_Name_Set (Writes),
                                 --  These are left as empty sets
                                 Proof_Calls           => Name_Sets.Empty_Set,
                                 Definite_Calls        => Name_Sets.Empty_Set,
                                 Conditional_Calls     => Name_Sets.Empty_Set,
                                 Local_Variables       => Name_Sets.Empty_Set,
                                 Local_Subprograms     => Name_Sets.Empty_Set,
                                 Local_Definite_Writes => Name_Sets.Empty_Set);
                           end;

                        else
                           --  Use (Yannick's) Computed Globals info
                           --  to add a GG entry to the ALI file.
                           declare
                              Reads  : Name_Sets.Set;
                              Writes : Name_Sets.Set;
                              Calls  : Name_Sets.Set;
                           begin
                              --  Collect the computed globals using only info
                              --  from the current compilation unit.
                              Collect_Direct_Computed_Globals (E,
                                                               Reads,
                                                               Writes,
                                                               Calls);

                              Global_Info := Global_Phase_1_Info'
                                (Name                  => To_Entity_Name (E),
                                 Kind                  =>
                                   (case Ekind (E) is
                                    when E_Entry     => Kind_Entry,
                                    when E_Function
                                       | E_Procedure => Kind_Subprogram,
                                    when E_Task_Type => Kind_Task,
                                    when others      => raise Program_Error),
                                 Origin                => Origin_Frontend,
                                 Inputs_Proof          => Name_Sets.Empty_Set,
                                 Inputs                => Reads,
                                 Outputs               => Writes,
                                 Proof_Calls           => Name_Sets.Empty_Set,
                                 Definite_Calls        => Name_Sets.Empty_Set,
                                 Conditional_Calls     => Calls,
                                 Local_Variables       => Name_Sets.Empty_Set,
                                 Local_Subprograms     => Name_Sets.Empty_Set,
                                 Local_Definite_Writes => Name_Sets.Empty_Set);
                           end;
                        end if;

                        Routines_With_Spec_Only.Append (Global_Info);

                     end;
                  end if;
               end if;

            when E_Package =>
               declare
                  Pkg_Body : constant Entity_Id :=
                    Defining_Entity (Package_Body (E),
                                     Empty_On_Errors => True);

               begin
                  if SPARK_Util.Analysis_Requested (E, With_Inlined => True)
                    and then Entity_Spec_In_SPARK (E)
                    and then not In_Predefined_Unit (E)
                    and then not Is_Wrapper_Package (E)
                    --  We do not generate graphs for wrapper packages of
                    --  subprogram instantiations since messages emitted on
                    --  them would be confusing.
                  then
                     if Present (Pkg_Body) then
                        if Entity_Body_In_SPARK (E) then
                           pragma Assert
                             (Nkind (Pkg_Body) = N_Defining_Identifier and then
                              Ekind (Pkg_Body) = E_Package_Body);

                           FA_Graphs.Include
                             (Pkg_Body,
                              Flow_Analyse_Entity
                                (Pkg_Body, E, Generating_Globals));
                        else
                           null;
                           --  ??? warn that we can't flow analyze elaboration?
                        end if;
                     elsif Generating_Globals
                       or else not Unit_Requires_Body (E)
                     then
                        FA_Graphs.Include
                          (E,
                           Flow_Analyse_Entity (E, E, Generating_Globals));
                     end if;

                  end if;
               end;

            when others =>
               raise Program_Error;
         end case;
      end Build_Graphs_For_Entity;

   --  Start of processing for Build_Graphs_For_Compilation_Unit

   begin
      --  Initialize outputs
      Routines_With_Spec_Only := Global_Info_Lists.Empty_List;
      FA_Graphs               := Analysis_Maps.Empty_Map;

      Iterate_Entities (Build_Graphs_For_Entity'Access);
   end Build_Graphs_For_Compilation_Unit;

   ------------------------
   -- Flow_Analyse_CUnit --
   ------------------------

   procedure Flow_Analyse_CUnit (GNAT_Root : Node_Id) is
      Success : Boolean;
      Unused  : Global_Info_Lists.List;
   begin

      --  Check that classwide contracts conform to the legality rules laid
      --  out in SRM 6.1.6.
      Success := True;
      for E of Marked_Entities loop
         --  ??? why Marked_Entities and not Entities_To_Translate?
         if Is_Subprogram (E)
           and then SPARK_Util.Analysis_Requested (E, With_Inlined => True)
           and then Entity_In_SPARK (E)
         then
            Check_Classwide_Contracts (E, Success);
         end if;
      end loop;

      --  Process entities and construct graphs if necessary
      Build_Graphs_For_Compilation_Unit (FA_Graphs               => FA_Graphs,
                                         Routines_With_Spec_Only => Unused,
                                         Generating_Globals      => False);

      --  ??? Perform interprocedural analysis

      --  Analyse graphs and produce error messages
      for FA of FA_Graphs loop
         if Gnat2Why_Args.Flow_Advanced_Debug then
            Write_Line (Character'Val (8#33#) & "[32m" &
                          "Flow analysis (errors) for " &
                          FA.Kind'Img &
                          " " &
                          Character'Val (8#33#) & "[1m" &
                          Get_Name_String (Chars (FA.Analyzed_Entity)) &
                          Character'Val (8#33#) & "[0m");
         end if;

         Analysis.Sanity_Check (FA, Success);
         if Success then
            case FA.Kind is
               when Kind_Entry        |
                    Kind_Package      |
                    Kind_Package_Body |
                    Kind_Subprogram   =>
                  Analysis.Sanity_Check_Postcondition (FA, Success);

               when Kind_Task =>
                  --  No postconditions for tasks
                  null;
            end case;
         end if;

         if Success then
            FA.Dependency_Map := Compute_Dependency_Relation (FA);

            case FA.Kind is
               when Kind_Entry | Kind_Task | Kind_Subprogram =>
                  --  In "Prove" mode we do not care about unwritten
                  --  exports, ineffective statements, dead code and
                  --  incorrect Depends aspects.
                  if not Gnat2Why_Args.Prove_Mode then
                     Analysis.Find_Unwritten_Exports (FA);
                     if FA.No_Effects then
                        if not FA.Is_Main
                          and then not Is_Error_Signaling_Procedure
                                         (FA.Analyzed_Entity)
                          and then not Has_User_Supplied_Globals
                                         (FA.Analyzed_Entity)
                        then
                           Error_Msg_Flow
                             (FA       => FA,
                              --  ??? another message for entries and tasks
                              Msg      => "subprogram & has no effect",
                              N        => FA.Analyzed_Entity,
                              F1       => Direct_Mapping_Id
                                (FA.Analyzed_Entity),
                              Tag      => Ineffective,
                              Severity => Warning_Kind);
                        end if;
                     else
                        Analysis.Find_Ineffective_Imports_And_Unused_Objects
                          (FA);
                        Analysis.Find_Ineffective_Statements (FA);
                     end if;
                     Analysis.Find_Dead_Code (FA);
                     Analysis.Check_Depends_Contract (FA);
                  end if;
                  Analysis.Check_Aliasing (FA);
                  Analysis.Find_Use_Of_Uninitialized_Variables (FA);
                  if FA.Kind /= Kind_Task then
                     --  We exclude Tasks from these checks since they do not
                     --  have pre- and postconditions.
                     Analysis.Check_Prefixes_Of_Attribute_Old (FA);
                     Analysis.Check_CAE_In_Preconditions (FA);
                  end if;
                  Analysis.Find_Exports_Derived_From_Proof_Ins (FA);
                  Analysis.Analyse_Main (FA);
                  Analysis.Check_Function_For_Volatile_Effects (FA);
                  Analysis.Check_Constant_After_Elaboration (FA);

                  --  If no errors or warnings were found during flow
                  --  analysis of the subprogram then emit the
                  --  relevant claim.
                  if FA.No_Errors_Or_Warnings then
                     Register_Claim (Claim'(E    => FA.Analyzed_Entity,
                                            Kind => Claim_Effects));
                  end if;

               when Kind_Package | Kind_Package_Body =>
                  --  In "Prove" mode we do not care about hidden
                  --  unexposed state, ineffective statements, dead
                  --  code and impossible to initialize state
                  --  abstractions.
                  if not Gnat2Why_Args.Prove_Mode then
                     Analysis.Find_Hidden_Unexposed_State (FA);
                     Analysis.Find_Ineffective_Statements (FA);
                     Analysis.Find_Dead_Code (FA);
                     Analysis.Find_Impossible_To_Initialize_State (FA);
                  end if;
                  Analysis.Check_Aliasing (FA);
                  Analysis.Find_Non_Elaborated_State_Abstractions (FA);
                  Analysis.Find_Use_Of_Uninitialized_Variables (FA);
                  Analysis.Check_Initializes_Contract (FA);
                  if FA.Kind = Kind_Package_Body then
                     Analysis.Check_Elaborate_Body (FA);
                  end if;
            end case;
         end if;

         --  Check for potentially blocking operations in protected actions
         if FA.Kind = Kind_Entry
           or else (FA.Kind = Kind_Subprogram
                    and then Convention (FA.Analyzed_Entity) =
                      Convention_Protected)
         then
            --  ??? issue different warning if the blocking status is unknown
            if Is_Potentially_Blocking (FA.Analyzed_Entity) then
               Error_Msg_Flow
                 (FA       => FA,
                  Msg      => "potentially blocking operation " &
                    "in protected operation &",
                  N        => FA.Analyzed_Entity,
                  F1       => Direct_Mapping_Id (FA.Analyzed_Entity),
                  Severity => High_Check_Kind);
            end if;
         end if;
      end loop;

      --  Finally check concurrent accesses. This check is done for the whole
      --  compilation unit.
      Analysis.Check_Concurrent_Accesses (GNAT_Root);

      if Gnat2Why_Args.Flow_Advanced_Debug then
         Write_Line (Character'Val (8#33#) & "[33m" &
                       "Flow analysis complete for current CU" &
                       Character'Val (8#33#) & "[0m");
      end if;

      --  If an error was found then print all errors/warnings and return
      --  with an error status.

      if Found_Flow_Error then
         Errout.Finalize (Last_Call => True);
         Errout.Output_Messages;
         Exit_Program (E_Errors);
      end if;

      --  Finalize extra loop info available from Flow_Utility

      Freeze_Loop_Info;

   end Flow_Analyse_CUnit;

   ---------------------------
   -- Generate_Flow_Globals --
   ---------------------------

   procedure Generate_Flow_Globals (GNAT_Root : Node_Id) is
      Routines_With_Spec_Only : Global_Info_Lists.List;
   begin
      GG_Write_Initialize (GNAT_Root);

      --  Process entities and construct graphs if necessary
      Build_Graphs_For_Compilation_Unit
        (FA_Graphs               => FA_Graphs,
         Routines_With_Spec_Only => Routines_With_Spec_Only,
         Generating_Globals      => True);

      --  Write GG info for entities without graphs
      --
      --  Entities without graphs are those with a contract but no body
      --  in SPARK. For them we need to explicitly register accesses to
      --  unsynchronized states and variables that occur in contract.
      for S of Routines_With_Spec_Only loop
         GG_Register_Global_Info (GI => S);

         Register_Unsynch_Accesses : declare
            Tasking : Tasking_Info;

            procedure Collect_Unsynchronized_Globals (From : Name_Sets.Set);
            --  Collect unsynchronized globals accesses by S

            ------------------------------------
            -- Collect_Unsynchronized_Globals --
            ------------------------------------

            procedure Collect_Unsynchronized_Globals (From : Name_Sets.Set) is
               E : Entity_Id;
            begin
               for N of From loop
                  --  Exclude states and objects that are synchronized or are
                  --  Part_Of single concurrent types.
                  E := Find_Entity (N);

                  if not (Is_Synchronized_Object (E)
                          or else Is_Synchronized_State (E)
                          or else Is_Part_Of_Concurrent_Object (E))
                  then
                     Tasking (Unsynch_Accesses).Include (E);
                  end if;

               end loop;

            end Collect_Unsynchronized_Globals;

         begin
            if S.Origin = Origin_User then
               Collect_Unsynchronized_Globals (S.Inputs_Proof);
               Collect_Unsynchronized_Globals (S.Inputs);
               Collect_Unsynchronized_Globals (S.Outputs);

               GG_Register_Tasking_Info (S.Name, Tasking);
            end if;
         end Register_Unsynch_Accesses;
      end loop;

      --  Write GG info for entities with graphs
      for FA of FA_Graphs loop
         if Gnat2Why_Args.Flow_Advanced_Debug then
            Write_Line (Character'Val (8#33#) & "[32m" &
                          "Global generation (slice) for " &
                          FA.Kind'Img &
                          " " &
                          Character'Val (8#33#) & "[1m" &
                          Get_Name_String (Chars (FA.Analyzed_Entity)) &
                          Character'Val (8#33#) & "[0m");
            Indent;
         end if;

         if FA.Kind = Kind_Package_Body then
            --  Here we use the package's Refined_State aspect (if it exists).
            --  Note that we process this aspect regardless of whether we
            --  generate a gg graph or not.
            declare
               Refined_State_N : constant Node_Id :=
                 Get_Pragma (FA.Analyzed_Entity, Pragma_Refined_State);

            begin
               if Present (Refined_State_N) then
                  declare
                     DM : constant Dependency_Maps.Map :=
                       Parse_Refined_State (Refined_State_N);
                  begin
                     GG_Register_State_Info (DM);
                  end;
               end if;
            end;
         end if;

         if FA.GG.Aborted then
            if Gnat2Why_Args.Flow_Advanced_Debug then
               Write_Line ("aborted earlier");
            end if;
         else
            declare
               Inputs_Proof          : Node_Sets.Set;
               Inputs                : Node_Sets.Set;
               Outputs               : Node_Sets.Set;
               Proof_Calls           : Node_Sets.Set;
               Definite_Calls        : Node_Sets.Set;
               Conditional_Calls     : Node_Sets.Set;
               Local_Variables       : Node_Sets.Set;
               Local_Subprograms     : Node_Sets.Set;
               Local_Definite_Writes : Node_Sets.Set;
               Global_Info           : Global_Phase_1_Info;
            begin
               Compute_Globals (FA,
                                Inputs_Proof          => Inputs_Proof,
                                Inputs                => Inputs,
                                Outputs               => Outputs,
                                Proof_Calls           => Proof_Calls,
                                Definite_Calls        => Definite_Calls,
                                Conditional_Calls     => Conditional_Calls,
                                Local_Variables       => Local_Variables,
                                Local_Subprograms     => Local_Subprograms,
                                Local_Definite_Writes =>
                                  Local_Definite_Writes);

               if Gnat2Why_Args.Flow_Advanced_Debug then
                  Write_Str ("Proof inputs         : ");
                  Print_Node_Set (Inputs_Proof);

                  Write_Str ("Inputs               : ");
                  Print_Node_Set (Inputs);

                  Write_Str ("Outputs              : ");
                  Print_Node_Set (Outputs);

                  Write_Str ("Proof calls          : ");
                  Print_Node_Set (Proof_Calls);

                  Write_Str ("Definite calls       : ");
                  Print_Node_Set (Definite_Calls);

                  Write_Str ("Conditional calls    : ");
                  Print_Node_Set (Conditional_Calls);

                  Write_Str ("Local variables      : ");
                  Print_Node_Set (Local_Variables);

                  Write_Str ("Local subprograms    : ");
                  Print_Node_Set (Local_Subprograms);

                  if FA.Kind in Kind_Package | Kind_Package_Body then
                     Write_Str ("Local definite writes: ");
                     Print_Node_Set (Local_Definite_Writes);
                  end if;
               end if;

               Global_Info := Global_Phase_1_Info'
                 (Name                  =>
                    To_Entity_Name (if FA.Kind = Kind_Package_Body
                                    then Spec_Entity (FA.Analyzed_Entity)
                                    else FA.Analyzed_Entity),
                  Kind                  => FA.Kind,
                  Origin                => Origin_Flow,
                  Inputs_Proof          => To_Name_Set (Inputs_Proof),
                  Inputs                => To_Name_Set (Inputs),
                  Outputs               => To_Name_Set (Outputs),
                  Proof_Calls           => To_Name_Set (Proof_Calls),
                  Definite_Calls        => To_Name_Set (Definite_Calls),
                  Conditional_Calls     => To_Name_Set (Conditional_Calls),
                  Local_Variables       => To_Name_Set (Local_Variables),
                  Local_Subprograms     => To_Name_Set (Local_Subprograms),
                  Local_Definite_Writes =>
                    To_Name_Set (Local_Definite_Writes));

               GG_Register_Global_Info (GI => Global_Info);
            end;

         end if;

         if Gnat2Why_Args.Flow_Advanced_Debug then
            Outdent;
         end if;

      end loop;

      GG_Write_Finalize;

      if Gnat2Why_Args.Flow_Advanced_Debug then
         Write_Line (Character'Val (8#33#) & "[33m" &
                       "Global generation complete for current CU" &
                       Character'Val (8#33#) & "[0m");
      end if;
   end Generate_Flow_Globals;

   -----------------------------
   -- Last_Statement_Is_Raise --
   -----------------------------

   function Last_Statement_Is_Raise (E : Entity_Id) return Boolean is
      Last_Statement : constant Node_Id :=
        Last (Statements (Handled_Statement_Sequence (Get_Body (E))));
   begin
      return Nkind (Last_Statement) in N_Raise_xxx_Error | N_Raise_Statement;
   end Last_Statement_Is_Raise;

end Flow;
