------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                                 F L O W                                  --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--              Copyright (C) 2013-2025, Capgemini Engineering              --
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
with Ada.Directories;
with Ada.Strings.Maps;
with Ada.Strings;
with Ada.Strings.Fixed;
with Ada.Text_IO;
with Assumptions;                      use Assumptions;
with Atree;                            use Atree;
with Errout_Wrapper;                   use Errout_Wrapper;
with Flow.Analysis;
with Flow.Control_Dependence_Graph;
with Flow.Control_Flow_Graph;
with Flow.Data_Dependence_Graph;
with Flow.Interprocedural;
with Flow.Program_Dependence_Graph;
with Flow_Sanity;
with Flow.Slice;                       use Flow.Slice;
with Flow_Classwide;                   use Flow_Classwide;
with Flow_Debug;                       use Flow_Debug;
with Flow_Generated_Globals;           use Flow_Generated_Globals;
with Flow_Generated_Globals.Partial;
with Flow_Generated_Globals.Traversal; use Flow_Generated_Globals.Traversal;
with Flow_Generated_Globals.Phase_2;   use Flow_Generated_Globals.Phase_2;
with Flow_Error_Messages;              use Flow_Error_Messages;
with Flow_Refinement;                  use Flow_Refinement;
with Flow_Utility;                     use Flow_Utility;
with Gnat2Why.Assumptions;             use Gnat2Why.Assumptions;
with Gnat2Why_Args;
with GNATCOLL.JSON;                    use GNATCOLL.JSON;
with Namet;                            use Namet;
with Output;                           use Output;
with Sem_Ch7;                          use Sem_Ch7;
with Sem_Util;                         use Sem_Util;
with Sinfo.Nodes;                      use Sinfo.Nodes;
with Sinfo.Utils;                      use Sinfo.Utils;
with Sinput;                           use Sinput;
with Snames;                           use Snames;
with SPARK_Definition;                 use SPARK_Definition;
with SPARK_Definition.Annotate;        use SPARK_Definition.Annotate;
with SPARK_Frame_Conditions;           use SPARK_Frame_Conditions;
with SPARK_Util;                       use SPARK_Util;
with SPARK_Util.Subprograms;           use SPARK_Util.Subprograms;
with Sprint;                           use Sprint;
with String_Utils;                     use String_Utils;
with VC_Kinds;                         use VC_Kinds;
with Why;

package body Flow is

   --  These debug options control which graphs to output.

   Debug_Print_CFG           : constant Boolean := True;
   Debug_Print_Intermediates : constant Boolean := False;
   Debug_Print_PDG           : constant Boolean := True;

   --  These debug options control some of the tracing produced.

   Debug_Trace_Scoping : constant Boolean := True;

   procedure Debug_Print_Generated_Contracts (FA : Flow_Analysis_Graphs);
   --  Pretty print all contracts (for switch --flow-show-gg).

   ------------------------------------------------------------

   use Flow_Graphs;

   Whitespace : constant Ada.Strings.Maps.Character_Set :=
     Ada.Strings.Maps.To_Set
       (Ada.Characters.Latin_1.Space
        & Ada.Characters.Latin_1.CR
        & Ada.Characters.Latin_1.LF);

   Linebreak : constant Ada.Strings.Maps.Character_Set :=
     Ada.Strings.Maps.To_Set
       (Ada.Characters.Latin_1.CR & Ada.Characters.Latin_1.LF);

   procedure Build_Graphs_For_Analysis (FA_Graphs : out Analysis_Maps.Map);
   --  Build flow graphs for the current compilation unit; phase 2

   procedure Check_Handler_Accesses;
   --  Check Handler'Access expressions in the current compilation unit

   procedure Check_Specification_Contracts;
   --  Perform initial checks on contracts:
   --  * classwide contracts conform to the legality rules laid out in SRM
   --  6.1.6.
   --  * global contracts do not use constants without variable input as per
   --  SRM 6.1.4(16)
   --  We do this for requested subprograms from the current unit whose spec
   --  has SPARK_Mode => On, regardless of the SPARK_Mode on their bodies.

   -------------------------------------
   -- Debug_Print_Generated_Contracts --
   -------------------------------------

   procedure Debug_Print_Generated_Contracts (FA : Flow_Analysis_Graphs) is
      procedure Print_Named_Flow_Id_Set
        (Name : String; S : Flow_Id_Sets.Set; Print_Empty : Boolean);
      --  Debug procedure to pretty print the contents of S, indended under
      --  Name.

      -----------------------------
      -- Print_Named_Flow_Id_Set --
      -----------------------------

      procedure Print_Named_Flow_Id_Set
        (Name : String; S : Flow_Id_Sets.Set; Print_Empty : Boolean) is
      begin
         if not S.Is_Empty or else Print_Empty then
            Write_Str (Name);
            if not S.Is_Empty then
               Write_Str (" =>");
            end if;
            Write_Eol;
            Indent;
            for E of To_Ordered_Flow_Id_Set (S) loop
               Sprint_Flow_Id (E);
               Write_Eol;
            end loop;
            Outdent;
         end if;
      end Print_Named_Flow_Id_Set;

      --  Start of processing for Debug_Print_Generated_Contracts

   begin
      Write_Str ("Generated contracts for ");
      Write_Str (Full_Source_Name (FA.Spec_Entity));
      Write_Eol;
      Indent;

      if FA.Kind = Kind_Package then
         declare
            M : constant Dependency_Maps.Map :=
              GG_Get_Initializes (FA.Spec_Entity);

            Ordered_LHS : Ordered_Flow_Id_Sets.Set;
            --  To reliably print the Initializes contract on different
            --  operating systems we must sort the LHS items; the RHS will
            --  be sorted in the dedicated pretty-printing routine.

         begin
            if not M.Is_Empty then
               Write_Str ("Initializes =>");
               Write_Eol;
               Indent;

               for C in M.Iterate loop
                  Ordered_LHS.Insert (Dependency_Maps.Key (C));
               end loop;

               for LHS of Ordered_LHS loop
                  Print_Named_Flow_Id_Set
                    (Flow_Id_To_String (LHS), M (LHS), True);
               end loop;
               Outdent;
            end if;
         end;
      else
         declare
            use type Flow_Id_Sets.Set;

            procedure Print (Globals : Global_Flow_Ids);
            --  Pretty-print the globals

            -----------
            -- Print --
            -----------

            procedure Print (Globals : Global_Flow_Ids) is
               Inputs : constant Flow_Id_Sets.Set :=
                 Change_Variant (Globals.Inputs, Normal_Use);

               Outputs : constant Flow_Id_Sets.Set :=
                 Change_Variant (Globals.Outputs, Normal_Use);

               RO : constant Flow_Id_Sets.Set := Inputs - Outputs;
               RW : constant Flow_Id_Sets.Set := Inputs and Outputs;
               WO : constant Flow_Id_Sets.Set := Outputs - Inputs;

            begin
               Print_Named_Flow_Id_Set ("Proof_In", Globals.Proof_Ins, False);

               Print_Named_Flow_Id_Set ("Input", RO, False);
               Print_Named_Flow_Id_Set ("In_Out", RW, False);
               Print_Named_Flow_Id_Set ("Output", WO, False);
            end Print;

            Globals : Global_Flow_Ids;

         begin
            GG_Get_Globals
              (E => FA.Spec_Entity, S => FA.S_Scope, Globals => Globals);
            Write_Str ("Global =>");
            Write_Eol;
            Indent;
            Print (Globals);
            Outdent;

            GG_Get_Globals
              (E => FA.Spec_Entity, S => FA.B_Scope, Globals => Globals);
            Write_Str ("Refined_Global =>");
            Write_Eol;
            Indent;
            Print (Globals);
            Outdent;
         end;
      end if;

      Outdent;
   end Debug_Print_Generated_Contracts;

   Flow_GGs : JSON_Array;
   --  Each call of Flow_Analyse_Entity appends JSON-formatted GG information
   --  to this array.

   procedure Write_Flow_GG_To_JSON_File (Arr : JSON_Array);
   --  Writes out to disk a JSON file of flow analysis' generated globals

   procedure GG_To_JSON (FA : Flow_Analysis_Graphs; Arr : in out JSON_Array);
   --  Convert the flow-analysis generated contracts from FA to JSON format

   --------------------------------
   -- Write_Flow_GG_To_JSON_File --
   --------------------------------

   procedure Write_Flow_GG_To_JSON_File (Arr : JSON_Array) is
      FD        : Ada.Text_IO.File_Type;
      File_Name : constant String :=
        Ada.Directories.Compose (Name => Unit_Name, Extension => "gg");
      Full      : constant JSON_Value := Create_Object;

   begin
      Set_Field (Full, "contracts", Create (Arr));
      Ada.Text_IO.Create (FD, Ada.Text_IO.Out_File, File_Name);
      Ada.Text_IO.Put (FD, GNATCOLL.JSON.Write (Full, Compact => False));
      Ada.Text_IO.Close (FD);
   end Write_Flow_GG_To_JSON_File;

   ----------------
   -- GG_To_JSON --
   ----------------

   procedure GG_To_JSON (FA : Flow_Analysis_Graphs; Arr : in out JSON_Array) is
      function To_JSON (S : Flow_Id_Sets.Set) return JSON_Array
      with Pre => (for all Obj of S => Obj.Variant = Normal_Use);
      --  Returns the generated globals for the given set, if any, for the
      --  current program unit.

      function To_JSON (Globals : Global_Flow_Ids) return JSON_Value;
      --  Returns the generated globals for all modes (Input, In_Out, Output,
      --  Proof_In) for the current program unit.

      function To_JSON (E : Entity_Id) return JSON_Value
      with
        Pre  => Is_Global_Entity (E),
        Post => Kind (To_JSON'Result) = JSON_String_Type;
      --  Returns the full source name for E

      function To_JSON return JSON_Value;
      --  Returns the generated globals and refined globals for the current
      --  program unit.

      -------------
      -- To_JSON --
      -------------

      function To_JSON return JSON_Value is
         Globals : Global_Flow_Ids;
         Result  : constant JSON_Value := Create_Object;

      begin
         for Refined in Boolean'Range loop
            GG_Get_Globals
              (E       => FA.Spec_Entity,
               S       => (if Refined then FA.B_Scope else FA.S_Scope),
               Globals => Globals);

            Set_Field
              (Result,
               Standard_Ada_Case
                 (Get_Name_String
                    (if Refined then Name_Refined_Global else Name_Global)),
               To_JSON (Globals));
         end loop;

         --  Result looks like:
         --
         --  {"Global":
         --      {"Input": ["X", "Y", ..], "Proof_In": ..},
         --   "Refined_Global":
         --      {"Input": .. }
         --  }
         --
         --  or, if there are no globals:
         --  {"Global": {}, "Refined_Global": ..}
         return Result;
      end To_JSON;

      function To_JSON (Globals : Global_Flow_Ids) return JSON_Value is
         Result : constant JSON_Value := Create_Object;

         procedure Set_Field_Unless_Empty
           (Name : Name_Id; S : Flow_Id_Sets.Set);
         --  Only append to Result if S is non-empty

         -----------------------------
         --  Set_Field_Unless_Empty --
         -----------------------------

         procedure Set_Field_Unless_Empty
           (Name : Name_Id; S : Flow_Id_Sets.Set)
         is
            Obj : constant JSON_Array := To_JSON (S);

         begin
            if not Is_Empty (Obj) then
               Set_Field
                 (Result, Standard_Ada_Case (Get_Name_String (Name)), Obj);
            end if;
         end Set_Field_Unless_Empty;

         --  Local variables

         use type Flow_Id_Sets.Set;
         Inputs  : constant Flow_Id_Sets.Set :=
           Change_Variant (Globals.Inputs, Normal_Use);
         Outputs : constant Flow_Id_Sets.Set :=
           Change_Variant (Globals.Outputs, Normal_Use);

         --  Start of processing for To_JSON

      begin
         Set_Field_Unless_Empty
           (Name_Proof_In, Change_Variant (Globals.Proof_Ins, Normal_Use));
         Set_Field_Unless_Empty (Name_Input, Inputs - Outputs);
         Set_Field_Unless_Empty (Name_In_Out, Inputs and Outputs);
         Set_Field_Unless_Empty (Name_Output, Outputs - Inputs);

         --  Result looks like:
         --  {"Proof_In": ["X", "Y", ..]}, "Input": ["X"], ..}
         return Result;
      end To_JSON;

      function To_JSON (S : Flow_Id_Sets.Set) return JSON_Array is
         Variables : JSON_Array;

      begin
         for F of To_Ordered_Flow_Id_Set (S) loop
            case F.Kind is
               when Direct_Mapping =>
                  if not Is_Heap_Variable (F.Node) then
                     Append (Variables, To_JSON (F.Node));
                  end if;

               when Magic_String =>
                  if not Is_Heap_Variable (F.Name) then
                     Append (Variables, Create (Pretty_Print (F.Name)));
                  end if;

               when others =>
                  raise Program_Error;
            end case;
         end loop;

         --  Result looks like:
         --  Result = {"Proof_In": ["Outer.Inner.X", "Outer.Inner.Y", ..]}, or
         --  Result = {"Input"   : ...}, or
         --  Result = {"Output"  : ...}, ..
         return Variables;
      end To_JSON;

      function To_JSON (E : Entity_Id) return JSON_Value is
      begin
         --  Looks like:
         --  "Outer.Inner.X"
         return Create (Full_Source_Name (E));
      end To_JSON;

      --  Local variables

      Obj : JSON_Value;

      --  Start of processing for GG_To_JSON

   begin
      --  ??? ignore generated Initializes for now
      if FA.Kind = Kind_Package then
         return;
      end if;

      --  We ignore subprograms that came from a generic instance
      if Present (Enclosing_Generic_Instance (FA.Spec_Entity)) then
         return;
      end if;

      Obj := To_JSON;

      if not Is_Empty (Obj) then
         declare
            Result : constant JSON_Value := Create_Object;
            Slc    : constant Source_Ptr :=
              Sloc (Enclosing_Declaration (FA.Spec_Entity));
            File   : constant String := File_Name (Slc);
            Line   : constant Positive :=
              Positive (Get_Physical_Line_Number (Slc));
            Col    : constant Positive := Positive (Get_Column_Number (Slc));

         begin
            Set_Field (Result, "file", File);
            Set_Field (Result, "line", Line);
            Set_Field (Result, "col", Col);
            Set_Field (Result, "globals", Obj);
            Append (Arr, Result);
         end;
      end if;

   end GG_To_JSON;

   ------------------------
   -- Print_Graph_Vertex --
   ------------------------

   pragma Annotate (Xcov, Exempt_On, "Debugging code");
   procedure Print_Graph_Vertex
     (G : Flow_Graphs.Graph; M : Attribute_Maps.Map; V : Flow_Graphs.Vertex_Id)
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

      function Flow_Id_Image (F : Flow_Id) return String
      is ((case F.Kind is
             when Direct_Mapping =>
               (if Nkind (Get_Direct_Mapping_Id (F)) in N_Entity
                then Flow_Id_To_String (F)
                else Node_Or_Entity_Id'Image (Get_Direct_Mapping_Id (F))),
             when others => Flow_Id_To_String (F))
          & "|"
          & F.Variant'Img);

      --  Start of processing for Print_Graph_Vertex

   begin
      Write_Line
        ("Graph vertex ["
         & Natural'Image (G.Vertex_To_Natural (V))
         & "] ("
         & Flow_Id_Image (F)
         & "):");

      Indent;

      Format_Item ("Is_Null_Node", Boolean'Image (A.Is_Null_Node));
      Format_Item
        ("Is_Exceptional_Branch", Boolean'Image (A.Is_Exceptional_Branch));
      Format_Item
        ("Is_Exceptional_Path", Boolean'Image (A.Is_Exceptional_Path));
      Format_Item ("Is_Program_Node", Boolean'Image (A.Is_Program_Node));
      Format_Item
        ("Is_Original_Program_Node",
         Boolean'Image (A.Is_Original_Program_Node));
      Format_Item ("Is_Assertion", Boolean'Image (A.Is_Assertion));
      Format_Item ("Is_Default_Init", Boolean'Image (A.Is_Default_Init));
      Format_Item ("Is_Loop_Entry", Boolean'Image (A.Is_Loop_Entry));
      Format_Item ("Is_Initialized", Boolean'Image (A.Is_Initialized));
      Format_Item ("Is_Global", Boolean'Image (A.Is_Global));
      Format_Item ("Is_Import", Boolean'Image (A.Is_Import));
      Format_Item ("Is_Export", Boolean'Image (A.Is_Export));
      Format_Item ("Mode", Param_Mode'Image (A.Mode));
      Format_Item ("Is_Constant", Boolean'Image (A.Is_Constant));
      Format_Item ("Is_Callsite", Boolean'Image (A.Is_Callsite));
      Format_Item ("Is_Parameter", Boolean'Image (A.Is_Parameter));
      Format_Item
        ("Is_Global_Parameter", Boolean'Image (A.Is_Global_Parameter));
      Format_Item ("Is_Neverending", Boolean'Image (A.Is_Neverending));
      Format_Item
        ("Is_Declaration_Node", Boolean'Image (A.Is_Declaration_Node));
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
      Print_Node_Set (To_Subprograms (A.Subprogram_Calls));

      Write_Str ("Variables_Explicitly_Used: ");
      Print_Node_Set (A.Variables_Explicitly_Used);

      Outdent;
   end Print_Graph_Vertex;
   pragma Annotate (Xcov, Exempt_Off);

   --------------
   -- Is_Valid --
   --------------

   function Is_Valid (X : Flow_Analysis_Graphs_Root) return Boolean
   is (X.Kind
       = (case Ekind (X.Spec_Entity) is
            when E_Function | E_Procedure | E_Entry => Kind_Subprogram,
            when E_Task_Type => Kind_Task,
            when E_Package => Kind_Package,
            when others => raise Program_Error)
       and then (if not X.Generating_Globals
                 then
                   X.GG.Globals.Is_Empty
                   and then X.GG.Local_Variables.Is_Empty
                   and then X.Entries.Is_Empty
                   and then (for all Info of X.Tasking => Info.Is_Empty)));

   -----------------
   -- Print_Graph --
   -----------------

   pragma Annotate (Xcov, Exempt_On, "Debugging code");
   procedure Print_Graph
     (Filename               : String;
      G                      : Graph;
      M                      : Attribute_Maps.Map;
      Start_Vertex           : Vertex_Id := Null_Vertex;
      Helper_End_Vertex      : Vertex_Id := Null_Vertex;
      Exceptional_End_Vertex : Vertex_Id := Null_Vertex;
      End_Vertex             : Vertex_Id := Null_Vertex)
   is

      function NDI (G : Graph; V : Vertex_Id) return Node_Display_Info;
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

      function NDI (G : Graph; V : Vertex_Id) return Node_Display_Info is
         Rv : Node_Display_Info :=
           Node_Display_Info'
             (Show        => True,
              Shape       => Node_Shape_T'First,
              Colour      => Null_Unbounded_String,
              Fill_Colour => Null_Unbounded_String,
              Label       => Null_Unbounded_String);

         F : Flow_Id renames G.Get_Key (V);
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

         procedure Append_To_Label (S : String);
         --  Append S to Rv.Label

         ----------------------
         -- Append_To_Label  --
         ----------------------

         procedure Append_To_Label (S : String) is
         begin
            --  Leading whitespace occurs when a node image takes several lines
            --  (e.g. on complex expressions in the source or when a linebreak
            --  is added when pretty-printing aspects); trailing whitespace is
            --  added by the node printing routine anyway. Trim both.

            Append
              (Rv.Label, Ada.Strings.Fixed.Trim (S, Whitespace, Linebreak));
         end Append_To_Label;

         Output_Buffer : constant Saved_Output_Buffer := Save_Output_Buffer;
         --  Store previous buffer and indentation settings

         --  Start of processing for NDI

      begin
         Set_Special_Output (Append_To_Label'Unrestricted_Access);

         if A.Is_Exceptional_Path then
            Rv.Fill_Colour := To_Unbounded_String ("gold");
         end if;

         if A.Is_Null_Node then
            Rv.Show := False;

         elsif V = Start_Vertex then
            Write_Str ("start");
            Rv.Shape := Shape_None;
            Rv.Show :=
              G.In_Neighbour_Count (V) > 0
              or else G.Out_Neighbour_Count (V) > 0;

         elsif V = Helper_End_Vertex then
            Write_Str ("helper end");
            Rv.Shape := Shape_None;
            Rv.Show :=
              G.In_Neighbour_Count (V) > 0
              or else G.Out_Neighbour_Count (V) > 0;

         elsif V = Exceptional_End_Vertex then
            Write_Str ("exceptional end");
            Rv.Shape := Shape_None;
            Rv.Show :=
              G.In_Neighbour_Count (V) > 0
              or else G.Out_Neighbour_Count (V) > 0;

         elsif V = End_Vertex then
            Write_Str ("end");
            Rv.Shape := Shape_None;
            Rv.Show :=
              G.In_Neighbour_Count (V) > 0
              or else G.Out_Neighbour_Count (V) > 0;

         elsif F.Kind = Synthetic_Null_Export then
            case F.Variant is
               when Initial_Value =>
                  Rv.Show := False;

               when Final_Value =>
                  Rv.Colour := To_Unbounded_String ("chartreuse");
                  Rv.Shape := Shape_None;
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

            --  Record self-assignments are represented with two vertices;
            --  and one of them has Variables_Defined empty.

            if A.Variables_Defined.Is_Empty then
               null;

            --  Otherwise there might be multiple components being defined
            --  by the same inputs.

            else
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

               Write_Str (" => ");
            end if;

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

         elsif A.Pretty_Print_Kind = Pretty_Print_Package then
            Write_Str
              ("package "
               & Get_Name_String
                   (Chars (Defining_Entity (Get_Direct_Mapping_Id (F)))));

         elsif A.Pretty_Print_Kind = Pretty_Print_Reclaim then
            Write_Str ("reclaim");

         elsif A.Pretty_Print_Kind = Pretty_Print_Call_Exception then
            Rv.Shape := Shape_Diamond;
            Write_Str ("call exception");

         elsif A.Pretty_Print_Kind = Pretty_Print_Param_Havoc then
            Rv.Shape := Shape_Diamond;
            Write_Str ("param havoc");

         elsif A.Pretty_Print_Kind = Pretty_Print_Param_Scrub then
            Rv.Shape := Shape_None;
            Write_Str ("param scrub");

         elsif A.Pretty_Print_Kind = Pretty_Print_Program_Exit then
            Rv.Shape := Shape_None;
            Write_Str ("program exit");

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

               when Out_View =>
                  pragma Assert (A.Parameter_Formal.Kind = Direct_Mapping);
                  pragma Assert (A.Parameter_Actual.Kind = Direct_Mapping);
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
                  Write_Str ("'in");

               when Out_View =>
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

            pragma Assert (not Present (F));

         else
            if A.Is_Assertion then
               Rv.Shape := Shape_None;
               Write_Str ("assertion ");
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

                        when N_Block_Statement =>
                           pragma
                             Assert
                               (Nkind (Original_Node (N))
                                in N_Subprogram_Call);
                           Rv.Shape := Shape_Box;
                           Write_Str ("inlined call ");
                           Print_Node (Original_Node (N));

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
                              --  Basic loop
                              Write_Str ("loop");
                           elsif Present (Condition (Iteration_Scheme (N)))
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

                  if Is_Volatile (F) then
                     Write_Str ("\nvolatile:");
                     if Has_Async_Readers (F) then
                        Write_Str (NBSP & "AR");
                     end if;
                     if Has_Async_Writers (F) then
                        Write_Str (NBSP & "AW");
                     end if;
                     if Has_Effective_Reads (F) then
                        Write_Str (NBSP & "ER");
                     end if;
                     if Has_Effective_Writes (F) then
                        Write_Str (NBSP & "EW");
                     end if;
                  end if;

                  if not A.Is_Initialized then
                     Rv.Colour := To_Unbounded_String ("red");
                  elsif Is_Discriminant (F) or else Is_Record_Tag (F) then
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

            if not A.Loops.Is_Empty
              and then not (A.Is_Parameter or A.Is_Global_Parameter)
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

         if not A.Variables_Read.Is_Empty then
            Write_Str ("\nVR: {");
            declare
               First : Boolean := True;
            begin
               for F of A.Variables_Read loop
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

         if not A.Subprogram_Calls.Is_Empty then
            Write_Str ("\nSC: {");
            declare
               First : Boolean := True;
            begin
               for E of To_Subprograms (A.Subprogram_Calls) loop
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

         if A.Is_Assertion then
            Write_Str ("\nASSERT");
         end if;

         Write_Str ("\n<VId:" & Natural'Image (G.Vertex_To_Natural (V)) & ">");

         Write_Eol;
         Cancel_Special_Output;
         Restore_Output_Buffer (Output_Buffer);

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
           Edge_Display_Info'
             (Show   => True,
              Shape  => Edge_Normal,
              Colour => Null_Unbounded_String,
              Label  => Null_Unbounded_String);
      begin
         case Colour is
            when EC_Default =>
               null;

            when EC_Barrier =>
               Rv.Colour := To_Unbounded_String ("gold");
               Rv.Label := To_Unbounded_String ("barrier");

            when EC_Abend =>
               --  Using the same colour as for barriers, since this one
               --  won't ever show up normally (we prune all such paths).
               --  But in some debug modes you can see it, and they are
               --  reasonably similar...
               Rv.Colour := To_Unbounded_String ("gold");
               Rv.Label := To_Unbounded_String ("abend");

            when EC_Inf =>
               Rv.Colour := To_Unbounded_String ("chartreuse"); --  Hi Martin!
               Rv.Label := To_Unbounded_String ("inf");

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
   pragma Annotate (Xcov, Exempt_Off);

   -------------------------
   -- Flow_Analyse_Entity --
   -------------------------

   function Flow_Analyse_Entity
     (E : Entity_Id; Generating_Globals : Boolean) return Flow_Analysis_Graphs
   is
      FA :
        Flow_Analysis_Graphs_Root
          (Kind =>
             (case Ekind (E) is
                when E_Function | E_Procedure | E_Entry => Kind_Subprogram,
                when E_Task_Type => Kind_Task,
                when E_Package => Kind_Package,
                when others => raise Program_Error),
           Generating_Globals => Generating_Globals);

      Phase : constant String :=
        (if Generating_Globals then "Global generation" else "Flow analysis");

      procedure Debug (Str : String);
      --  Write debug string

      procedure Debug (Str : String; V : Boolean);
      --  Write debug string followed by yes or no, depending on V

      procedure Debug
        (Condition : Boolean; Graph : Flow_Graphs.Graph; Suffix : String);
      --  If Condition is True then dump Graph to file with Suffix file name;
      --  otherwise, do nothing.

      procedure Debug_GG_Source;
      --  Dump information about the source of GG information; only in phase 1

      -----------
      -- Debug --
      -----------

      pragma Annotate (Xcov, Exempt_On, "Debugging code");

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

      procedure Debug
        (Condition : Boolean; Graph : Flow_Graphs.Graph; Suffix : String) is
      begin
         if Condition then
            Print_Graph
              (Filename               =>
                 To_String (FA.Base_Filename) & "_" & Suffix,
               G                      => Graph,
               M                      => FA.Atr,
               Start_Vertex           => FA.Start_Vertex,
               Helper_End_Vertex      => FA.Helper_End_Vertex,
               Exceptional_End_Vertex => FA.Exceptional_End_Vertex,
               End_Vertex             => FA.End_Vertex);
         end if;
      end Debug;

      pragma Annotate (Xcov, Exempt_Off);

      ---------------------
      -- Debug_GG_Source --
      ---------------------

      pragma Annotate (Xcov, Exempt_On, "Debugging code");
      procedure Debug_GG_Source is
      begin
         if Gnat2Why_Args.Flow_Advanced_Debug and then FA.Generating_Globals
         then
            case FA.Kind is
               when Kind_Subprogram | Kind_Task =>
                  if not FA.Is_Generative then
                     Debug
                       ("skipped"
                        & (if Present (FA.Global_N)
                           then "(global found)"
                           elsif Present (FA.Depends_N)
                           then "(depends found)"
                           else "pure"));
                  end if;

                  Debug ("Spec in SPARK: ", Entity_In_SPARK (E));
                  Debug ("Body in SPARK: ", Entity_Body_In_SPARK (E));

               when Kind_Package =>
                  if not FA.Is_Generative then
                     Debug ("skipped (package spec)");
                     if Entity_Body_In_SPARK (FA.Spec_Entity) then
                        Debug ("skipped (package body)");
                     end if;
                  else
                     Debug ("Spec in SPARK: ", True);
                     if Entity_Body_In_SPARK (FA.Spec_Entity) then
                        Debug ("Body in SPARK: ", True);
                     end if;
                  end if;
            end case;
         end if;
      end Debug_GG_Source;
      pragma Annotate (Xcov, Exempt_Off);

      --  Start of processing for Flow_Analyse_Entity

   begin
      Current_Error_Node := E;

      FA.Spec_Entity := E;
      FA.Start_Vertex := Null_Vertex;
      FA.Helper_End_Vertex := Null_Vertex;
      FA.Exceptional_End_Vertex := Null_Vertex;
      FA.End_Vertex := Null_Vertex;
      FA.CFG := Create;
      FA.DDG := Create;
      FA.CDG := Create;
      FA.TDG := Create;
      FA.PDG := Create;
      FA.Errors_Or_Warnings := False;
      FA.Data_Dependency_Errors := False;
      FA.Flow_Dependency_Errors := False;
      FA.Has_Only_Terminating_Constructs := True;
      FA.Has_Only_Nonblocking_Statements := True;
      FA.Has_Only_Exceptional_Paths := False;

      --  Generate Globals (gg) or Flow Analysis (fa)
      FA.Base_Filename :=
        To_Unbounded_String (if Generating_Globals then "gg_" else "fa_");

      case Ekind (E) is
         when E_Entry | E_Task_Type | E_Function | E_Procedure =>
            --  For subprograms without explicit specs Get_Flow_Scope always
            --  return the Body_Part; however, Visible_Part for the spec scope
            --  is still fine and enables some sanity-checking assertions.

            FA.B_Scope := (Ent => E, Part => Body_Part);
            FA.S_Scope := (Ent => E, Part => Visible_Part);

            Append (FA.Base_Filename, "subprogram_");

            FA.Is_Main :=
              (case Ekind (E) is
                 when E_Function | E_Procedure =>
                   Might_Be_Main (E) or else Is_Interrupt_Handler (E),
                 when E_Entry => False,
                 when E_Task_Type => True,
                 when others => raise Program_Error);

            FA.Depends_N := Find_Contract (E, Pragma_Depends);
            FA.Global_N := Find_Contract (E, Pragma_Global);

            FA.Refined_Depends_N := Find_Contract (E, Pragma_Refined_Depends);
            FA.Refined_Global_N := Find_Contract (E, Pragma_Refined_Global);

            FA.Is_Generative := Refinement_Needed (E);

         when E_Package =>
            if Entity_Body_In_SPARK (E) then
               FA.B_Scope := (Ent => E, Part => Body_Part);

               Append (FA.Base_Filename, "pkg_body_");
            elsif Private_Spec_In_SPARK (E) then
               FA.B_Scope := (Ent => E, Part => Private_Part);

               Append (FA.Base_Filename, "pkg_priv_");
            else
               FA.B_Scope := (Ent => E, Part => Visible_Part);

               Append (FA.Base_Filename, "pkg_spec_");
            end if;

            FA.S_Scope := (Ent => E, Part => Visible_Part);

            FA.Initializes_N := Get_Pragma (E, Pragma_Initializes);

            FA.Is_Generative := No (FA.Initializes_N);

         when others =>
            raise Program_Error;
      end case;

      Append (FA.Base_Filename, Unique_Name (E));

      pragma Annotate (Xcov, Exempt_On, "Debugging code");
      if Gnat2Why_Args.Flow_Advanced_Debug then
         Write_Line
           (Character'Val (8#33#)
            & "[32m"
            & Phase
            & " (cons) of "
            & FA.Kind'Img
            & " "
            & Character'Val (8#33#)
            & "[1m"
            & Get_Name_String (Chars (E))
            & Character'Val (8#33#)
            & "[0m");

         Indent;

         if Debug_Trace_Scoping and not FA.Generating_Globals then
            Write_Str ("Spec_Scope: ");
            Print_Flow_Scope (FA.S_Scope);
            Write_Eol;
            declare
               Ptr : Flow_Scope := FA.S_Scope;
            begin
               Indent;
               while Present (Ptr) loop
                  case Declarative_Part'(Ptr.Part) is
                     when Body_Part =>
                        Ptr.Part := Private_Part;

                     when Private_Part | Visible_Part =>
                        Ptr := Get_Enclosing_Flow_Scope (Ptr);
                  end case;
                  if Present (Ptr) then
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
      pragma Annotate (Xcov, Exempt_Off);

      Debug_GG_Source;

      --  Print generated globals or initializes if --flow-show-gg is set
      if not Generating_Globals
        and then Gnat2Why_Args.Flow_Show_GG
        and then FA.Is_Generative
      then
         Debug_Print_Generated_Contracts (FA);
         GG_To_JSON (FA, Flow_GGs);
      end if;

      --  Even if aborting we still need to collect tasking-related info,
      --  (using control-flow traversal) and register the results.
      Control_Flow_Graph.Create (FA);

      --  Print this graph now in case the other algorithms barf
      Debug (Debug_Print_CFG, FA.CFG, "pruned");

      if not FA.Generating_Globals or else FA.Is_Generative then
         Control_Dependence_Graph.Create (FA);

         --  Restore the original CFG

         FA.CFG.Move (Source => FA.Full_CFG);
         FA.Atr.Move (Source => FA.Full_Atr);

         --  We can only print the original graph now, after FA.Atr has been
         --  restored.

         Debug (Debug_Print_CFG, FA.CFG, "cfg");

         Data_Dependence_Graph.Create (FA);
         Interprocedural.Create (FA);
         Program_Dependence_Graph.Create (FA);

         Debug (Debug_Print_Intermediates, FA.CDG, "cdg");
         Debug (Debug_Print_Intermediates, FA.DDG, "ddg");
         Debug (Debug_Print_PDG, FA.PDG, "pdg");
      end if;

      pragma Annotate (Xcov, Exempt_On, "Debugging code");
      if Gnat2Why_Args.Flow_Advanced_Debug then
         Outdent;
      end if;
      pragma Annotate (Xcov, Exempt_Off);

      return FA;

   end Flow_Analyse_Entity;

   -------------------------------
   -- Build_Graphs_For_Analysis --
   -------------------------------

   procedure Build_Graphs_For_Analysis (FA_Graphs : out Analysis_Maps.Map) is

      procedure Build_Graphs_For_Entity (E : Entity_Id);
      --  Build flow analysis graphs for the entity represented by the Subtree

      -----------------------------
      -- Build_Graphs_For_Entity --
      -----------------------------

      procedure Build_Graphs_For_Entity (E : Entity_Id) is
         Build : Boolean;

      begin
         for Child of Scope_Map (E) loop
            Build_Graphs_For_Entity (Child);
         end loop;

         case Container_Scope'(Ekind (E)) is
            when Entry_Kind | E_Function | E_Procedure | E_Task_Type =>

               --  Only analyse if requested, body is in SPARK and is annotated
               --  with SPARK_Mode => On.

               Build :=
                 Analysis_Requested (E, With_Inlined => True)
                 and then Entity_In_SPARK (E)
                 and then Entity_Body_In_SPARK (E);

               --  The above test will be false for null procedures, but we
               --  still need to mark them as skipped if they have the pragma
               --  Skip_Flow_And_Proof.

               if Entity_In_SPARK (E)
                 and then Is_Null_Procedure (E)
                 and then Has_Skip_Flow_And_Proof_Annotation (E)
               then
                  Skipped_Flow_And_Proof.Insert (E);
               end if;

            when E_Package =>
               --  Build graphs only when requested, the package is in SPARK
               --  and it is annotated with SPARK_Mode => On.
               --
               --  Do not generate graphs for wrapper packages of subprogram
               --  instantiations since messages emitted on them would be
               --  confusing.

               Build :=
                 Analysis_Requested (E, With_Inlined => True)
                 and then Entity_In_SPARK (E)
                 and then Entity_Spec_In_SPARK (E)
                 and then not Is_Ignored_Internal (E)
                 and then not Is_Wrapper_Package (E);

            when E_Protected_Type =>
               --   ??? perhaps we should do something, but now we don't
               Build := False;
         end case;

         if Build then
            FA_Graphs.Insert
              (Key      => E,
               New_Item =>
                 Flow_Analyse_Entity (E, Generating_Globals => False));
         end if;

      end Build_Graphs_For_Entity;

      --  Start of processing for Build_Graphs_For_Analysis

   begin
      if Present (Root_Entity) then
         Build_Graphs_For_Entity (Root_Entity);

         if Gnat2Why_Args.Flow_Show_GG and then not Is_Empty (Flow_GGs) then
            Write_Flow_GG_To_JSON_File (Flow_GGs);
            Clear (Flow_GGs);
         end if;

      end if;
   end Build_Graphs_For_Analysis;

   ----------------------------
   -- Check_Handler_Accesses --
   ----------------------------

   procedure Check_Handler_Accesses is
   begin
      for N of SPARK_Definition.Handler_Accesses loop
         declare
            Context : constant Entity_Id := Find_Enclosing_Scope (N);
            Subp    : constant Entity_Id := Entity (Prefix (N));
            Globals : Global_Flow_Ids;
            Unused  : Boolean;
            use type Flow_Id_Sets.Set;
         begin
            if Is_In_Analyzed_Files (Context) then
               Get_Globals
                 (Subprogram          => Subp,
                  Scope               => (Ent => Subp, Part => Visible_Part),
                  Classwide           => False,
                  Globals             => Globals,
                  Use_Deduced_Globals => True,
                  Ignore_Depends      => False);

               for Var of
                 To_Ordered_Flow_Id_Set
                   (Globals.Proof_Ins or Globals.Inputs or Globals.Outputs)
               loop
                  if not Is_Synchronized (Var) then
                     Error_Msg_Flow
                       (E          => Context,
                        Msg        =>
                          "handler & with unsychchronized global &",
                        N          => N,
                        Severity   => Medium_Check_Kind,
                        Tag        => Concurrent_Access,
                        Suppressed => Unused,
                        F1         => Direct_Mapping_Id (Subp),
                        F2         => Var);
                  end if;
               end loop;
            end if;
         end;
      end loop;
   end Check_Handler_Accesses;

   -----------------------------------
   -- Check_Specification_Contracts --
   -----------------------------------

   procedure Check_Specification_Contracts is
      procedure Check_Contracts (E : Entity_Id);
      --  Check contracts for a given program unit and its nested units

      ---------------------
      -- Check_Contracts --
      ---------------------

      procedure Check_Contracts (E : Entity_Id) is
      begin
         for Child of Scope_Map (E) loop
            Check_Contracts (Child);
         end loop;

         if Ekind (E) in Entry_Kind | E_Function | E_Procedure | E_Task_Type
           and then SPARK_Util.Subprograms.Analysis_Requested
                      (E, With_Inlined => True)
           and then Entity_Spec_In_SPARK (E)
         then
            --  We emit similar check messages if we analyse a body, so to
            --  avoid duplication don't emit them here.
            --  ??? ideally we should emit all messages from one place
            if not Entity_Body_In_SPARK (E) then
               Analysis.Check_Constant_Global_Contracts (E);
            end if;

            if Is_Subprogram (E) then
               Check_Classwide_Contracts (E);
            end if;
         end if;
      end Check_Contracts;

      --  Start of processing for Check_Specification_Contracts

   begin
      if Present (Root_Entity) then
         Check_Contracts (Root_Entity);
      end if;
   end Check_Specification_Contracts;

   ------------------------
   -- Flow_Analyse_CUnit --
   ------------------------

   procedure Flow_Analyse_CUnit
     (GNAT_Root : Node_Id; Found_Error : out Boolean)
   is
      FA_Graphs : Analysis_Maps.Map := Analysis_Maps.Empty_Map;
      --  All analysis results are stashed here in case we need them later
      --  (e.g. for inter-procedural flow analysis).

      Success : Boolean;

   begin
      Found_Error := False;

      Check_Handler_Accesses;
      Check_Specification_Contracts;

      --  Process entities and construct graphs if necessary
      Build_Graphs_For_Analysis (FA_Graphs => FA_Graphs);

      --  ??? Perform interprocedural analysis

      --  Analyse graphs and produce error messages
      for FA of FA_Graphs loop
         pragma Annotate (Xcov, Exempt_On, "Debugging code");
         if Gnat2Why_Args.Flow_Advanced_Debug then
            Write_Line
              (Character'Val (8#33#)
               & "[32m"
               & "Flow analysis (errors) for "
               & FA.Kind'Img
               & " "
               & Character'Val (8#33#)
               & "[1m"
               & Get_Name_String (Chars (FA.Spec_Entity))
               & Character'Val (8#33#)
               & "[0m");
         end if;
         pragma Annotate (Xcov, Exempt_Off);

         Analysis.Sanity_Check (FA, Success);

         if Success then
            FA.Dependency_Map := Compute_Dependency_Relation (FA);

            case FA.Kind is
               when Kind_Task | Kind_Subprogram =>
                  --  In "Prove" mode we do not care about unwritten exports,
                  --  ineffective statements, dead code and incorrect Depends
                  --  aspects.
                  if Gnat2Why_Args.Mode /= GPM_Prove then
                     Analysis.Find_Unwritten_Exports (FA);
                     Analysis.Find_Ineffective_Imports_And_Unused_Objects (FA);
                     Analysis.Find_Ineffective_Statements (FA);
                     Analysis.Find_Stable_Conditions (FA);
                     Analysis.Find_Dead_Code (FA);
                     Analysis.Check_Depends_Contract (FA);
                  end if;
                  Analysis.Check_Aliasing (FA);
                  Analysis.Find_Use_Of_Uninitialized_Variables (FA);
                  if FA.Kind /= Kind_Task then
                     --  We exclude tasks from these checks since they do not
                     --  have pre- and postconditions.
                     Analysis.Check_Prefixes_Of_Attribute_Old (FA);
                     Analysis.Check_CAE_In_Preconditions (FA);
                     --  We exclude tasks from this check since it is only
                     --  relevant for subprograms.
                     Analysis.Check_Always_Terminates (FA);
                     Analysis.Check_Ghost_Subprogram_Outputs (FA);
                  end if;
                  Analysis.Check_Ghost_Calls_Policy (FA);
                  Analysis.Check_Ghost_Terminates (FA);
                  Analysis.Find_Input_Only_Used_In_Assertions (FA);
                  Analysis.Find_Illegal_Reads_Of_Proof_Ins (FA);
                  Analysis.Check_Function_For_Volatile_Effects (FA);
                  Analysis.Check_Output_Constant_After_Elaboration (FA);

                  --  If no errors or warnings were found during flow
                  --  analysis of the subprogram then emit the
                  --  relevant claim.
                  if not FA.Errors_Or_Warnings then
                     Register_Claim
                       (Claim'(E => FA.Spec_Entity, Kind => Claim_Effects));
                  end if;

               when Kind_Package =>
                  declare
                     Have_Full_Package_Code : constant Boolean :=
                       not Unit_Requires_Body
                             (FA.Spec_Entity, Do_Abstract_States => True)
                       or else Present (Body_Entity (FA.Spec_Entity));
                     --  Some analysis only makes sense if we have already the
                     --  full code for a package, i.e. it is not just the spec
                     --  that needs to be completed by a body.

                  begin
                     --  In "Prove" mode we do not care about hidden unexposed
                     --  state, ineffective statements, dead code and
                     --  impossible to initialize state abstractions.
                     if Gnat2Why_Args.Mode /= GPM_Prove then
                        Analysis.Find_Ineffective_Statements (FA);
                        Analysis.Find_Stable_Conditions (FA);
                        Analysis.Find_Dead_Code (FA);
                        Analysis.Check_Hidden_State (FA);
                        if Have_Full_Package_Code then
                           Analysis.Find_Impossible_To_Initialize_State (FA);
                        end if;
                     end if;
                     Analysis.Check_Aliasing (FA);
                     if Present
                          (SPARK_Util.Subprograms.Enclosing_Subprogram
                             (FA.Spec_Entity))
                     then
                        Analysis.Check_Potentially_Blocking (FA);
                     end if;
                     Analysis.Check_Always_Terminates (FA);
                     Analysis.Check_Ghost_Terminates (FA);
                     if Have_Full_Package_Code then
                        Analysis.Find_Use_Of_Uninitialized_Variables (FA);
                        Analysis.Check_Initializes_Contract (FA);
                     end if;
                     Analysis.Check_Refined_State_Contract (FA);
                     Analysis.Check_Calls_With_Constant_After_Elaboration (FA);
                  end;
            end case;
         end if;

         --  Check for potentially blocking operations in protected actions and
         --  for calls to Current_Task from entry body.
         if Is_Protected_Operation (FA.Spec_Entity) then
            Flow.Analysis.Check_Potentially_Blocking (FA);

            --  Detect calls to Current_Task from entry bodies and interrupt
            --  handlers.

            if Ekind (FA.Spec_Entity) = E_Entry
              and then Calls_Current_Task (FA.Spec_Entity)
            then
               Error_Msg_Flow
                 (FA       => FA,
                  Msg      =>
                    "Current_Task should not be called from "
                    & "an entry body & (RM C.7.1(17))",
                  N        => FA.Spec_Entity,
                  F1       => Direct_Mapping_Id (FA.Spec_Entity),
                  Tag      => Call_To_Current_Task,
                  Severity => High_Check_Kind);
            end if;

            if Ekind (FA.Spec_Entity) = E_Procedure
              and then Is_Interrupt_Handler (FA.Spec_Entity)
              and then Calls_Current_Task (FA.Spec_Entity)
            then
               Error_Msg_Flow
                 (FA       => FA,
                  Msg      =>
                    "Current_Task should not be called from "
                    & "an interrupt handler & (RM C.7.1(17))",
                  N        => FA.Spec_Entity,
                  F1       => Direct_Mapping_Id (FA.Spec_Entity),
                  Tag      => Call_To_Current_Task,
                  Severity => High_Check_Kind);
            end if;

         end if;

         --  If no data/flow dependency errors has been detected, then emit an
         --  message with severity "info" and a fake "wrong" tag corresponding
         --  to the proved dependency; in summary table those messages will
         --  appear as "proved" by flow.

         case FA.Kind is
            when Kind_Subprogram | Kind_Task =>
               if Present (FA.Global_N) and then not FA.Data_Dependency_Errors
               then
                  Error_Msg_Flow
                    (FA       => FA,
                     Msg      => "data dependencies proved",
                     N        => FA.Global_N,
                     Tag      => Global_Wrong,
                     Severity => Info_Kind);
               end if;

               if Present (FA.Depends_N) and then not FA.Flow_Dependency_Errors
               then
                  Error_Msg_Flow
                    (FA       => FA,
                     Msg      => "flow dependencies proved",
                     N        => FA.Depends_N,
                     Tag      => Depends_Wrong,
                     Severity => Info_Kind);
               end if;

            when Kind_Package =>
               if Present (FA.Initializes_N)
                 and then not FA.Flow_Dependency_Errors
               then
                  Error_Msg_Flow
                    (FA       => FA,
                     Msg      => "flow dependencies proved",
                     N        => FA.Initializes_N,
                     Tag      => Depends_Wrong,
                     Severity => Info_Kind);
               end if;
         end case;

         --  Keep track of entities whose flow analysis has been "skipped",
         --  i.e. which actually have been analysed, but we only emitted
         --  error and not info/warning/check messages.

         if Has_Skip_Flow_And_Proof_Annotation (FA.Spec_Entity) then
            Skipped_Flow_And_Proof.Insert (FA.Spec_Entity);
         end if;
      end loop;

      --  Finally check concurrent accesses. This check is done for the whole
      --  compilation unit.
      Analysis.Check_Concurrent_Accesses (GNAT_Root);

      pragma Annotate (Xcov, Exempt_On, "Debugging code");
      if Gnat2Why_Args.Flow_Advanced_Debug then
         Write_Line
           (Character'Val (8#33#)
            & "[33m"
            & "Flow analysis complete for current CU"
            & Character'Val (8#33#)
            & "[0m");
      end if;
      pragma Annotate (Xcov, Exempt_Off);

      Flow_Sanity.Check_Incomplete_Globals;

      --  If an error was found then print all errors/warnings and return
      --  with an error status.

      if Found_Flow_Error then
         Found_Error := True;
      end if;

      --  Finalize extra loop info available from Flow_Utility

      Freeze_Loop_Info;

   end Flow_Analyse_CUnit;

   ----------------------
   -- Generate_Globals --
   ----------------------

   procedure Generate_Globals (GNAT_Root : Node_Id)
   renames Flow_Generated_Globals.Partial.Generate_Contracts;

   ----------
   -- Hash --
   ----------

   function Hash (E : Entry_Call) return Ada.Containers.Hash_Type is
      use type Ada.Containers.Hash_Type;

   begin
      --  ??? constants for hashing are picked from the air
      return
        Ada.Containers.Hash_Type (E.Prefix)
        * 17
        + Ada.Containers.Hash_Type (E.Entr) * 19;
   end Hash;

end Flow;
