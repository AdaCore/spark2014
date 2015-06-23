------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                                 F L O W                                  --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                  Copyright (C) 2013-2015, Altran UK Limited              --
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
with Ada.Strings;                   use Ada.Strings;

with Assumptions;                   use Assumptions;
with Gnat2Why.Assumptions;          use Gnat2Why.Assumptions;
with Gnat2Why_Args;
with Why;

with SPARK_Definition;              use SPARK_Definition;
with SPARK_Util;                    use SPARK_Util;

with Flow.Analysis;
with Flow.Control_Dependence_Graph;
with Flow.Control_Flow_Graph;
with Flow.Data_Dependence_Graph;
with Flow.Interprocedural;
with Flow.Program_Dependence_Graph;
with Flow.Slice;                    use Flow.Slice;
with Flow_Classwide;                use Flow_Classwide;
with Flow_Generated_Globals;        use Flow_Generated_Globals;
with Flow_Debug;                    use Flow_Debug;
with Flow_Error_Messages;           use Flow_Error_Messages;
with Flow_Utility;                  use Flow_Utility;

with Errout;                        use Errout;
with Lib;                           use Lib;
with Namet;                         use Namet;
with Nlists;                        use Nlists;
with Osint;                         use Osint;
with Output;                        use Output;
with Sem_Aux;                       use Sem_Aux;
with Sem_Util;                      use Sem_Util;
with Sem_Ch7;                       use Sem_Ch7;
with Sinfo;                         use Sinfo;
with Snames;                        use Snames;
with Sprint;                        use Sprint;

with SPARK_Frame_Conditions;        use SPARK_Frame_Conditions;
with VC_Kinds;                      use VC_Kinds;

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
   use Info_Sets;

   Temp_String : Unbounded_String := Null_Unbounded_String;

   Whitespace : constant Ada.Strings.Maps.Character_Set :=
     Ada.Strings.Maps.To_Set
       (" " & Ada.Characters.Latin_1.CR & Ada.Characters.Latin_1.LF);

   procedure Add_To_Temp_String (S : String);
   --  Nasty nasty hack to add the given string to a global variable,
   --  Temp_String. We use this to pretty print nodes via Sprint_Node.

   function Flow_Analyse_Entity (E               : Entity_Id;
                                 S               : Node_Id;
                                 Compute_Globals : Boolean)
                                 return Flow_Analysis_Graphs
     with Pre  => Ekind (E) in Subprogram_Kind  |
                               E_Task_Type      |
                               E_Protected_Type |
                               E_Entry          |
                               E_Package        |
                               E_Package_Body,
          Post => Is_Valid (Flow_Analyse_Entity'Result);
   --  Flow analyse the given entity E with a specification node S (i.e. where
   --  the N_Contract node is attached). Do nothing for entities with no body
   --  or not in SPARK 2014.

   procedure Build_Graphs_For_Compilation_Unit
     (Compute_Globals : Boolean;
      FA_Graphs       : out Analysis_Maps.Map;
      Info_Set        : out Info_Sets.Set)
     with Post => (if not Compute_Globals then
                     Info_Set = Info_Sets.Empty_Set);
   --  Build all flow graphs for the current compilation unit

   function Last_Statement_Is_Raise (E : Entity_Id) return Boolean
     with Pre => Ekind (E) in Subprogram_Kind | E_Task_Type | E_Entry;
   --  Returns True if the last statement in the
   --  Handled_Sequence_Of_Statements of subprogram E is an
   --  N_Raise_Statement.

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
      return 3 * Flow_Graphs.Vertex_Hash (VD.To) + 5 *
        Flow_Graphs.Vertex_Hash (VD.From);
   end Vertex_Pair_Hash;

   ------------------------
   -- Print_Graph_Vertex --
   ------------------------

   procedure Print_Graph_Vertex (G : Flow_Graphs.T;
                                 M : Attribute_Maps.Map;
                                 V : Flow_Graphs.Vertex_Id)
   is
      F : constant Flow_Id      := G.Get_Key (V);
      A : constant V_Attributes := M (V);

      procedure Format_Item (K, V : String);

      function Flow_Id_Image (F : Flow_Id) return String;

      procedure Format_Item (K, V : String)
      is
      begin
         Write_Str (K);
         Write_Str (": ");
         Write_Str (V);
         Write_Eol;
      end Format_Item;

      function Flow_Id_Image (F : Flow_Id) return String
      is
         R : Unbounded_String;
      begin
         case F.Kind is
            when Direct_Mapping =>
               if Nkind (F.Node) in N_Entity then
                  Append (R, Flow_Id_To_String (F));
               else
                  Append (R, Node_Or_Entity_Id'Image (F.Node));
               end if;
            when others =>
               Append (R, Flow_Id_To_String (F));
         end case;

         Append (R, "|");

         Append (R, Flow_Id_Variant'Image (F.Variant));

         return To_String (R);
      end Flow_Id_Image;

   begin
      Write_Str ("Graph vertex [" &
                   Natural'Image (G.Vertex_To_Natural (V)) &
                   "] (" &
                   Flow_Id_Image (F) &
                   "):");
      Write_Eol;

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
        when E_Subprogram_Body =>
           Is_Subprogram (X.Analyzed_Entity),
        when E_Task_Body =>
           Ekind (X.Analyzed_Entity) = E_Task_Type,
        when E_Entry =>
           Ekind (X.Analyzed_Entity) = E_Entry,
        when E_Protected_Type =>
           Ekind (X.Analyzed_Entity) = E_Protected_Type,
        when E_Package =>
           Ekind (X.Analyzed_Entity) = E_Package,
        when E_Package_Body =>
           Ekind (X.Analyzed_Entity) = E_Package_Body)
           and then (if not X.Compute_Globals
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
   -- Print_Graph --
   -----------------

   procedure Print_Graph
     (Filename          : String;
      G                 : T;
      M                 : Attribute_Maps.Map;
      Start_Vertex      : Vertex_Id := Null_Vertex;
      Helper_End_Vertex : Vertex_Id := Null_Vertex;
      End_Vertex        : Vertex_Id := Null_Vertex) is

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
           (Show        => True,
            Shape       => Node_Shape_T'First,
            Colour      => Null_Unbounded_String,
            Fill_Colour => Null_Unbounded_String,
            Label       => Null_Unbounded_String);

         F : constant Flow_Id      := G.Get_Key (V);
         A : constant V_Attributes := M (V);

         procedure Print_Node (N : Node_Id);

         ----------------
         -- Print_Node --
         ----------------

         procedure Print_Node (N : Node_Id)
         is
         begin
            pg (Union_Id (N));
         end Print_Node;

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
                  Print_Node (A.Parameter_Formal.Node);
                  Write_Str ("'in");
                  Write_Str ("&nbsp;:=&nbsp;");
                  Print_Node (A.Parameter_Actual.Node);
                  if A.Is_Discr_Or_Bounds_Parameter then
                     Write_Str ("'discr_or_bounds");
                  end if;

               when Out_View =>
                  pragma Assert (A.Parameter_Formal.Kind = Direct_Mapping);
                  pragma Assert (A.Parameter_Actual.Kind = Direct_Mapping);
                  pragma Assert (not A.Is_Discr_Or_Bounds_Parameter);
                  Print_Node (A.Parameter_Actual.Node);
                  Write_Str ("&nbsp;:=&nbsp;");
                  Print_Node (A.Parameter_Formal.Node);
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

         elsif A.Is_Default_Init then
            Rv.Shape := Shape_None;

            Sprint_Flow_Id (A.Default_Init_Var);
            if Present (A.Default_Init_Val) then
               Write_Str ("&nbsp;is by default&nbsp;");
               Print_Node (A.Default_Init_Val);
            else
               Write_Str ("&nbsp;is initialized implicitly");
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
                              Print_Node
                                (Condition (Iteration_Scheme (N)));
                           else
                              Print_Node
                                (Iteration_Scheme (N));
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
                  if Is_Volatile (F) then
                     Write_Str ("\nvolatile:");
                     if Has_Async_Readers (F) then
                        Write_Str ("&nbsp;AR");
                     end if;
                     if Has_Async_Writers (F) then
                        Write_Str ("&nbsp;AW");
                     end if;
                     if Has_Effective_Reads (F) then
                        Write_Str ("&nbsp;ER");
                     end if;
                     if Has_Effective_Writes (F) then
                        Write_Str ("&nbsp;EW");
                     end if;
                  end if;

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

            if A.Loops.Length > 0 and not (A.Is_Parameter or
                                             A.Is_Global_Parameter)
            then
               Write_Str ("\nLoops:");
               for Loop_Identifier of A.Loops loop
                  Write_Str ("&nbsp;");
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

         if A.Variables_Used.Length > 0 then
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

         if A.Subprograms_Called.Length > 0 then
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

         if A.Variables_Defined.Length > 0 then
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

   function Flow_Analyse_Entity (E               : Entity_Id;
                                 S               : Node_Id;
                                 Compute_Globals : Boolean)
                                 return Flow_Analysis_Graphs
   is
      Tmp : Flow_Analysis_Graphs_Root
         (Kind            => (case Ekind (E) is
                              when Subprogram_Kind  => E_Subprogram_Body,
                              when E_Task_Type      => E_Task_Body,
                              when others           => Ekind (E)),
          Compute_Globals => Compute_Globals);

      Phase : constant String :=
        (if Compute_Globals
         then "Global generation"
         else "Flow analysis");
   begin
      Tmp.Analyzed_Entity              := E;
      Tmp.Spec_Node                    := S;
      Tmp.Start_Vertex                 := Null_Vertex;
      Tmp.Helper_End_Vertex            := Null_Vertex;
      Tmp.End_Vertex                   := Null_Vertex;
      Tmp.CFG                          := Create;
      Tmp.DDG                          := Create;
      Tmp.CDG                          := Create;
      Tmp.TDG                          := Create;
      Tmp.PDG                          := Create;
      Tmp.Atr                          := Attribute_Maps.Empty_Map;
      Tmp.Other_Fields                 := Vertex_To_Vertex_Set_Maps.Empty_Map;
      Tmp.Local_Constants              := Node_Sets.Empty_Set;
      Tmp.All_Vars                     := Flow_Id_Sets.Empty_Set;
      Tmp.Unmodified_Vars              := Node_Sets.Empty_Set;
      Tmp.Unreferenced_Vars            := Node_Sets.Empty_Set;
      Tmp.Loops                        := Node_Sets.Empty_Set;
      Tmp.Dependency_Map               := Dependency_Maps.Empty_Map;
      Tmp.No_Effects                   := False;
      Tmp.No_Errors_Or_Warnings        := True;
      Tmp.Direct_Calls                 := Node_Sets.Empty_Set;

      if Compute_Globals then
         --  Generate Globals
         Tmp.Base_Filename := To_Unbounded_String ("gg_");
      else
         --  Flow Analysis
         Tmp.Base_Filename := To_Unbounded_String ("fa_");
      end if;

      case Ekind (E) is
         when Subprogram_Kind =>
            Tmp.B_Scope := Get_Flow_Scope (Subprogram_Body (E));
            Tmp.S_Scope := Get_Flow_Scope (E);

            Append (Tmp.Base_Filename, "subprogram_");

            Tmp.Is_Main := Might_Be_Main (E);

            Tmp.Last_Statement_Is_Raise := Last_Statement_Is_Raise (E);

            Tmp.Depends_N := Get_Pragma (E, Pragma_Depends);
            Tmp.Global_N  := Get_Pragma (E, Pragma_Global);

            declare
               Body_E : constant Entity_Id := Subprogram_Body_Entity (E);
            begin
               Tmp.Refined_Depends_N := Get_Pragma (Body_E,
                                                    Pragma_Refined_Depends);
               Tmp.Refined_Global_N  := Get_Pragma (Body_E,
                                                    Pragma_Refined_Global);
            end;

            Tmp.Is_Generative := Refinement_Needed (E);

            Tmp.Function_Side_Effects_Present := False;

         when E_Entry =>
            Tmp.B_Scope := Get_Flow_Scope (Entry_Body (E));
            Tmp.S_Scope := Get_Flow_Scope (E);

            --  This is intentional, no clash here with functions and
            --  procedures.
            Append (Tmp.Base_Filename, "subprogram_");

            Tmp.Is_Main := False;

            Tmp.Last_Statement_Is_Raise := Last_Statement_Is_Raise (E);

            --  ??? O429-046 requires FE work for contracts on entries
            Tmp.Depends_N         := Empty;
            Tmp.Global_N          := Empty;
            Tmp.Refined_Depends_N := Empty;
            Tmp.Refined_Global_N  := Empty;

            Tmp.Is_Generative := Refinement_Needed (E);

            Tmp.Function_Side_Effects_Present := False;

         when E_Task_Type =>
            --  ??? O429-046 Set contract nodes

            Tmp.B_Scope := Get_Flow_Scope (Task_Body (E));
            Tmp.S_Scope := Get_Flow_Scope (E);

            Append (Tmp.Base_Filename, "task_");

            Tmp.Is_Main := True;

            Tmp.Last_Statement_Is_Raise := Last_Statement_Is_Raise (E);

            --  ??? O429-046 requires FE work for contracts on tasks
            Tmp.Depends_N         := Empty;
            Tmp.Global_N          := Empty;
            Tmp.Refined_Depends_N := Empty;
            Tmp.Refined_Global_N  := Empty;

            Tmp.Is_Generative := Refinement_Needed (E);

            Tmp.Function_Side_Effects_Present := False;

         when E_Protected_Type =>
            --  Note we're analyzing the definitions, and B_Scope should
            --  point to the thing we're actually analyzing. We do not
            --  analyze anything in the protected body itself since it
            --  can't contain anything but procedure and entry bodies.
            Tmp.B_Scope := Get_Flow_Scope (PO_Definition (E));
            Tmp.S_Scope := Get_Flow_Scope (E);

            Append (Tmp.Base_Filename, "po_");

         when E_Package =>
            Tmp.B_Scope       := Flow_Scope'(E, Private_Part);
            Tmp.S_Scope       := Flow_Scope'(E, Private_Part);

            Append (Tmp.Base_Filename, "pkg_spec_");

            Tmp.Initializes_N := Get_Pragma (E, Pragma_Initializes);

            Tmp.Visible_Vars  := Flow_Id_Sets.Empty_Set;

         when E_Package_Body =>
            Tmp.B_Scope       := Flow_Scope'(Spec_Entity (E), Body_Part);
            Tmp.S_Scope       := Flow_Scope'(Spec_Entity (E), Private_Part);

            Append (Tmp.Base_Filename, "pkg_body_");

            Tmp.Initializes_N := Get_Pragma (Spec_Entity (E),
                                             Pragma_Initializes);

            Tmp.Visible_Vars  := Flow_Id_Sets.Empty_Set;

         when others =>
            raise Why.Not_SPARK;
      end case;

      Tmp.GG.Aborted := False;
      Tmp.GG.Globals := Node_Sets.Empty_Set;

      declare
         FA : Flow_Analysis_Graphs := Tmp;
      begin
         Append (FA.Base_Filename, Unique_Name (E));

         if Gnat2Why_Args.Flow_Advanced_Debug then
            Write_Str (Character'Val (8#33#) & "[32m" &
                         Phase & " (cons) of " &
                         Entity_Kind'Image (FA.Kind) &
                         " " &
                         Character'Val (8#33#) & "[1m" &
                         Get_Name_String (Chars (E)) &
                         Character'Val (8#33#) & "[0m");
            Write_Eol;

            Indent;

            if Debug_Trace_Scoping and not FA.Compute_Globals then
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

         if FA.Compute_Globals then
            --  There are a number of cases where we don't want to produce
            --  graphs as we already have all the contracts we need.
            case FA.Kind is
               when E_Subprogram_Body | E_Task_Body | E_Entry =>
                  if not FA.Is_Generative then
                     if Gnat2Why_Args.Flow_Advanced_Debug then
                        if Present (FA.Global_N) then
                           Write_Line ("skipped (global found)");
                        elsif Present (FA.Depends_N) then
                           Write_Line ("skipped (depends found)");
                        else
                           raise Program_Error;
                        end if;
                     end if;
                     FA.GG.Aborted := True;
                  end if;

                  if Gnat2Why_Args.Flow_Advanced_Debug then
                     Write_Line ("Spec in SPARK: " & (if Entity_In_SPARK (E)
                                                      then "yes"
                                                      else "no"));
                     if FA.Kind = E_Subprogram_Body then
                        Write_Line ("Body in SPARK: " &
                                      (if Entity_Body_Valid_SPARK (E)
                                       then "yes"
                                       else "no"));
                     elsif FA.Kind = E_Task_Body then
                        Write_Line ("Body in SPARK: " &
                                      (if Entity_Body_Valid_SPARK
                                            (Task_Body_Entity (E))
                                       then "yes"
                                       else "no"));
                        --   ??? O429-046 need to do something for entries
                        --       here.
                     end if;
                  end if;

               when E_Protected_Type =>
                  --  ??? O429-046 we need to do something for globals here
                  if Gnat2Why_Args.Flow_Advanced_Debug then
                     Write_Str ("skipped (protected body)");
                     Write_Eol;
                  end if;
                  FA.GG.Aborted := True;

               when E_Package =>
                  if Gnat2Why_Args.Flow_Advanced_Debug then
                     Write_Line ("skipped (package spec)");
                  end if;
                  FA.GG.Aborted := True;

               when E_Package_Body =>
                  declare
                     Refined_State_N : constant Node_Id :=
                       Get_Pragma (E,
                                   Pragma_Refined_State);

                     DM              : Dependency_Maps.Map;
                     Constituents    : Flow_Id_Sets.Set;
                  begin
                     if Present (Refined_State_N) then
                        if Gnat2Why_Args.Flow_Advanced_Debug then
                           Write_Line ("Refinement found: yes");
                        end if;

                        DM := Parse_Refined_State (Refined_State_N);
                        if Gnat2Why_Args.Flow_Advanced_Debug then
                           for State in DM.Iterate loop
                              Write_Line ("State       :");
                              Indent;
                              Print_Flow_Id (Dependency_Maps.Key (State));
                              Outdent;
                              Write_Line ("Constituents:");
                              Constituents := Dependency_Maps.Element (State);
                              Indent;
                              for Constituent of Constituents loop
                                 Print_Flow_Id (Constituent);
                              end loop;
                              Outdent;
                           end loop;
                        end if;
                     else
                        if Gnat2Why_Args.Flow_Advanced_Debug then
                           Write_Line ("Refinement found: no");
                        end if;
                        FA.GG.Aborted := True;
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

         --  We print this graph first in case the other algorithms
         --  barf.
         if Debug_Print_CFG then
            Print_Graph (Filename          =>
                           To_String (FA.Base_Filename) & "_cfg",
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
                         G                 => FA.DDG,
                         M                 => FA.Atr,
                         Start_Vertex      => FA.Start_Vertex,
                         Helper_End_Vertex => FA.Helper_End_Vertex,
                         End_Vertex        => FA.End_Vertex);
         end if;

         if Debug_Print_PDG then
            Print_Graph (Filename          =>
                           To_String (FA.Base_Filename) & "_pdg",
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
      end;
   end Flow_Analyse_Entity;

   ---------------------------------------
   -- Build_Graphs_For_Compilation_Unit --
   ---------------------------------------

   procedure Build_Graphs_For_Compilation_Unit
     (Compute_Globals : Boolean;
      FA_Graphs       : out Analysis_Maps.Map;
      Info_Set        : out Info_Sets.Set)
   is
      Body_E : Entity_Id;
   begin
      --  Initialize the Info_Set to the empty set
      Info_Set := Info_Sets.Empty_Set;

      for E of Entity_Set loop
         case Ekind (E) is
            when E_Entry | E_Task_Type | Subprogram_Kind =>
               Body_E := (case Ekind (E) is
                          when E_Entry         => Entry_Body_Entity (E),
                          when E_Task_Type     => Task_Body_Entity (E),
                          when Subprogram_Kind => E,
                          when others          => raise Why.Unexpected_Node);

               if SPARK_Util.Analysis_Requested (Body_E) then
                  if Entity_Body_In_SPARK (Body_E)
                    and then Entity_Body_Valid_SPARK (Body_E)
                  then
                     --  Produce a GG graph
                     FA_Graphs.Include (E, Flow_Analyse_Entity
                                          (E,
                                           E,
                                           Compute_Globals));
                  elsif Compute_Globals then
                     declare
                        Scope        : constant Flow_Scope :=
                          Get_Flow_Scope (Body_E);
                        Global_Node  : constant Node_Id :=
                          Get_Contract_Node (E,
                                             Scope,
                                             Global_Contract);
                        Depends_Node : constant Node_Id :=
                          Get_Contract_Node (E,
                                             Scope,
                                             Depends_Contract);
                     begin
                        if Present (Global_Node)
                          or else Present (Depends_Node)
                        then
                           --  If we have a user-provided Global or
                           --  Depends contract then we use Get_Globals
                           --  to get that.

                           declare
                              Proof_Ins       : Flow_Id_Sets.Set;
                              Reads           : Flow_Id_Sets.Set;
                              Writes          : Flow_Id_Sets.Set;
                              Subprogram_Info : Subprogram_Phase_1_Info;
                           begin
                              Get_Globals (Subprogram           => E,
                                           Scope                => Scope,
                                           Classwide            => False,
                                           Proof_Ins            => Proof_Ins,
                                           Reads                => Reads,
                                           Writes               => Writes,
                                           Use_Computed_Globals => False);

                              Subprogram_Info := Subprogram_Phase_1_Info'
                                (Name              => To_Entity_Name (E),
                                 Kind              =>
                                   (case Ekind (E) is
                                    when E_Entry         => E_Kind,
                                    when E_Task_Type     => T_Kind,
                                    when Subprogram_Kind => S_Kind,
                                    when others          =>
                                      raise Why.Unexpected_Node),
                                 Globals_Origin    => UG,
                                 Inputs_Proof      => To_Name_Set (Proof_Ins),
                                 Inputs            => To_Name_Set (Reads),
                                 Outputs           => To_Name_Set (Writes),
                                 Proof_Calls       => Name_Set.Empty_Set,
                                 Definite_Calls    => Name_Set.Empty_Set,
                                 Conditional_Calls => Name_Set.Empty_Set,
                                 Local_Variables   => Name_Set.Empty_Set,
                                 Local_Subprograms => Name_Set.Empty_Set);

                              Info_Set.Include (Subprogram_Info);
                           end;

                        else
                           --  Use (Yannick's) Computed Globals info
                           --  to add a GG entry to the ALI file.
                           declare
                              Reads           : Name_Set.Set;
                              Writes          : Name_Set.Set;
                              Calls           : Name_Set.Set;
                              Subprogram_Info : Subprogram_Phase_1_Info;
                           begin
                              --  Collect the computed globals using
                              --  only info from the current
                              --  compilation unit.
                              Collect_Current_Computed_Globals (E,
                                                                Reads,
                                                                Writes,
                                                                Calls);

                              Subprogram_Info := Subprogram_Phase_1_Info'
                                (Name              => To_Entity_Name (E),
                                 Kind              =>
                                   (if Ekind (E) in Subprogram_Kind
                                    then S_Kind
                                    else T_Kind),
                                 Globals_Origin    => XR,
                                 Inputs_Proof      => Name_Set.Empty_Set,
                                 Inputs            => Reads,
                                 Outputs           => Writes,
                                 Proof_Calls       => Name_Set.Empty_Set,
                                 Definite_Calls    => Name_Set.Empty_Set,
                                 Conditional_Calls => Calls,
                                 Local_Variables   => Name_Set.Empty_Set,
                                 Local_Subprograms => Name_Set.Empty_Set);

                              Info_Set.Include (Subprogram_Info);
                           end;
                        end if;
                     end;
                  end if;
               end if;

            when E_Protected_Type =>
               --  !!! O429-046 Globals for protected objects
               if SPARK_Util.Analysis_Requested (E) then
                  FA_Graphs.Include (E, Flow_Analyse_Entity
                                       (E,
                                        E,
                                        Compute_Globals));
               end if;

            when E_Package =>
               declare
                  Pkg_Spec   : constant Node_Id := Package_Specification (E);
                  Pkg_Body   : Node_Id;
                  Needs_Body : Boolean := Unit_Requires_Body (E);
               begin
                  if SPARK_Util.Analysis_Requested (E)
                    and Entity_Spec_In_SPARK (E)
                    and not In_Predefined_Unit (E)
                    and not Is_Wrapper_Package (E)
                    --  We do not generate graphs for wrapper packages
                    --  of subprogram instantiations since messages
                    --  emitted on them would be confusing.
                  then
                     Pkg_Body := Pkg_Spec;
                     while Present (Pkg_Body) and then
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
                           Flow_Analyse_Entity (Pkg_Body, E, Compute_Globals));
                     elsif not Needs_Body then
                        FA_Graphs.Include
                          (E,
                           Flow_Analyse_Entity (E, E, Compute_Globals));
                     else
                        null;
                        --  ??? warn that we can't flow analyze elaboration?
                     end if;

                  end if;
               end;

            when others =>
               null;
         end case;
      end loop;
   end Build_Graphs_For_Compilation_Unit;

   ------------------------
   -- Flow_Analyse_CUnit --
   ------------------------

   procedure Flow_Analyse_CUnit is
      Success : Boolean;
      Unused  : Info_Sets.Set;
   begin

      --  Check that classwide contracts conform to the legality rules laid
      --  out in SRM 6.1.6.
      Success := True;
      for E of Entity_Set loop
         if Is_Subprogram (E)
           and then SPARK_Util.Analysis_Requested (E)
           and then Entity_In_SPARK (E)
         then
            Check_Classwide_Contracts (E, Success);
         end if;
      end loop;

      --  Process entities and construct graphs if necessary
      Build_Graphs_For_Compilation_Unit (Compute_Globals => False,
                                         FA_Graphs       => FA_Graphs,
                                         Info_Set        => Unused);

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
            case FA.Kind is
               when E_Entry           |
                    E_Package         |
                    E_Package_Body    |
                    E_Subprogram_Body =>
                  Analysis.Sanity_Check_Postcondition (FA, Success);
               when E_Protected_Type |
                    E_Task_Body      =>
                  --  No postconditions for tasks and pos.
                  null;
            end case;
         end if;
         if Success then
            FA.Dependency_Map := Compute_Dependency_Relation (FA);

            case FA.Kind is
               when E_Entry | E_Task_Body | E_Subprogram_Body =>
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
                             (FA   => FA,
                              Msg  => "subprogram & has no effect",
                              N    => FA.Analyzed_Entity,
                              F1   => Direct_Mapping_Id (FA.Analyzed_Entity),
                              Tag  => Ineffective,
                              Kind => Warning_Kind);
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
                  if FA.Kind /= E_Task_Body then
                     --  We exclude Tasks from this check since they don't
                     --  have pre and post conditions.
                     Analysis.Check_Prefixes_Of_Attribute_Old (FA);
                  end if;
                  Analysis.Find_Exports_Derived_From_Proof_Ins (FA);
                  Analysis.Analyse_Main (FA);
                  Analysis.Check_Function_For_Volatile_Effects (FA);
                  Analysis.Check_Constant_After_Elaboration (FA);

                  --  If no errors or warnings were found during flow
                  --  analysis of the subprogram then emit the
                  --  relevant claim.
                  if FA.No_Errors_Or_Warnings then
                     Register_Claim ((E    => FA.Analyzed_Entity,
                                      Kind => Claim_Effects));
                  end if;

               when E_Protected_Type =>
                  --  ??? O429-046 analyze POs
                  null;

               when E_Package | E_Package_Body =>
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
            end case;
         end if;

         --  Not really necessary, but it forces N131-017 to occur
         --  immediately, instead of when this procedure ends.
         FA.Atr.Clear;
      end loop;

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

      --  Finalize extra loop info available from Flow_Utility;

      Freeze_Loop_Info;

   end Flow_Analyse_CUnit;

   ---------------------------
   -- Generate_Flow_Globals --
   ---------------------------

   procedure Generate_Flow_Globals (GNAT_Root : Node_Id) is
      pragma Unreferenced (GNAT_Root);
      Info_Set : Info_Sets.Set;
   begin
      GG_Write_Initialize;

      --  Process entities and construct graphs if necessary
      Build_Graphs_For_Compilation_Unit (Compute_Globals => True,
                                         FA_Graphs       => FA_Graphs,
                                         Info_Set        => Info_Set);

      --  Consider the subprogram info in case a graph was not created
      for S of Info_Set loop
         GG_Write_Subprogram_Info (SI => S);
      end loop;

      --  Write Generated Globals to the ALI file
      for FA of FA_Graphs loop
         if Gnat2Why_Args.Flow_Advanced_Debug then
            Write_Line (Character'Val (8#33#) & "[32m" &
                          "Global generation (slice) for " &
                          Entity_Kind'Image (FA.Kind) &
                          " " &
                          Character'Val (8#33#) & "[1m" &
                          Get_Name_String (Chars (FA.Analyzed_Entity)) &
                          Character'Val (8#33#) & "[0m");
            Indent;
         end if;

         if FA.GG.Aborted then
            if Gnat2Why_Args.Flow_Advanced_Debug then
               Write_Line ("aborted earlier");
            end if;
         elsif FA.Kind in E_Subprogram_Body | E_Task_Body | E_Entry then
            declare
               Inputs_Proof      : Node_Sets.Set;
               Inputs            : Node_Sets.Set;
               Outputs           : Node_Sets.Set;
               Proof_Calls       : Node_Sets.Set;
               Definite_Calls    : Node_Sets.Set;
               Conditional_Calls : Node_Sets.Set;
               Local_Variables   : Node_Sets.Set;
               Local_Subprograms : Node_Sets.Set;
               Subprogram_Info   : Subprogram_Phase_1_Info;
            begin
               Compute_Globals (FA,
                                Inputs_Proof      => Inputs_Proof,
                                Inputs            => Inputs,
                                Outputs           => Outputs,
                                Proof_Calls       => Proof_Calls,
                                Definite_Calls    => Definite_Calls,
                                Conditional_Calls => Conditional_Calls,
                                Local_Variables   => Local_Variables,
                                Local_Subprograms => Local_Subprograms);

               if Gnat2Why_Args.Flow_Advanced_Debug then
                  Write_Str ("Proof inputs     : ");
                  Print_Node_Set (Inputs_Proof);

                  Write_Str ("Inputs           : ");
                  Print_Node_Set (Inputs);

                  Write_Str ("Outputs          : ");
                  Print_Node_Set (Outputs);

                  Write_Str ("Proof calls      : ");
                  Print_Node_Set (Proof_Calls);

                  Write_Str ("Definite calls   : ");
                  Print_Node_Set (Definite_Calls);

                  Write_Str ("Conditional calls: ");
                  Print_Node_Set (Conditional_Calls);

                  Write_Str ("Local variables  : ");
                  Print_Node_Set (Local_Variables);

                  Write_Str ("Local subprograms: ");
                  Print_Node_Set (Local_Subprograms);
               end if;

               Subprogram_Info := Subprogram_Phase_1_Info'
                 (Name              => To_Entity_Name (FA.Analyzed_Entity),
                  Kind              =>
                    (case FA.Kind is
                     when E_Subprogram_Body => S_Kind,
                     when E_Task_Body       => T_Kind,
                     when E_Entry           => E_Kind,
                     when others            => raise Why.Unexpected_Node),
                  Globals_Origin    => Flow_Generated_Globals.FA,
                  Inputs_Proof      => To_Name_Set (Inputs_Proof),
                  Inputs            => To_Name_Set (Inputs),
                  Outputs           => To_Name_Set (Outputs),
                  Proof_Calls       => To_Name_Set (Proof_Calls),
                  Definite_Calls    => To_Name_Set (Definite_Calls),
                  Conditional_Calls => To_Name_Set (Conditional_Calls),
                  Local_Variables   => To_Name_Set (Local_Variables),
                  Local_Subprograms => To_Name_Set (Local_Subprograms));

               GG_Write_Subprogram_Info (SI => Subprogram_Info);
            end;
         elsif FA.Kind = E_Package_Body then
            --  Here we utilize the package's Refined_State aspect
            declare
               Refined_State_N : constant Node_Id :=
                 Get_Pragma (FA.Analyzed_Entity,
                             Pragma_Refined_State);

               DM              : Dependency_Maps.Map;
            begin
               --  Sanity check that there is indeed a Refined_State
               --  aspect. Note that if there wasn't one, then GG
               --  would have been aborted earlier for this entity.
               pragma Assert (Present (Refined_State_N));

               DM := Parse_Refined_State (Refined_State_N);
               GG_Write_Package_Info (DM);
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
      Ptr : Node_Id;
   begin
      case Ekind (E) is
         when Subprogram_Kind =>
            Ptr := Subprogram_Body (E);
         when E_Task_Type =>
            Ptr := Task_Body (E);
         when E_Entry =>
            Ptr := Entry_Body (E);
         when others =>
            raise Why.Unexpected_Node;
      end case;
      Ptr := Last (Statements (Handled_Statement_Sequence (Ptr)));
      return Nkind (Ptr) in N_Raise_xxx_Error | N_Raise_Statement;
   end Last_Statement_Is_Raise;

end Flow;
