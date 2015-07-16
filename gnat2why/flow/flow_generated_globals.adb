------------------------------------------------------------------------------
--                                                                          --
--                           GNAT2WHY COMPONENTS                            --
--                                                                          --
--               F L O W . C O M P U T E D _ G L O B A L S                  --
--                                                                          --
--                                B o d y                                   --
--                                                                          --
--               Copyright (C) 2014-2015, Altran UK Limited                 --
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

with Ada.Containers.Hashed_Maps;
with Ada.Containers.Hashed_Sets;
with Ada.Strings.Maps;           use Ada.Strings.Maps;
with Ada.Strings.Unbounded;      use Ada.Strings.Unbounded;
with Ada.Text_IO.Unbounded_IO;   use Ada.Text_IO.Unbounded_IO;
with Ada.Text_IO;                use Ada.Text_IO;

with AA_Util;                    use AA_Util;
with ALI;                        use ALI;
with Lib.Util;                   use Lib.Util;
with Namet;                      use Namet;
with Osint.C;                    use Osint.C;
with Osint;                      use Osint;
with Output;                     use Output;
with Sem_Util;                   use Sem_Util;
with Sinfo;                      use Sinfo;

with Gnat2Why_Args;
with Hashing;                    use Hashing;
with SPARK_Frame_Conditions;     use SPARK_Frame_Conditions;
with SPARK_Util;                 use SPARK_Util;

with Flow_Utility;               use Flow_Utility;
with Flow_Debug;                 use Flow_Debug;
with Graph;

package body Flow_Generated_Globals is

   use type Flow_Id_Sets.Set;
   use type Name_Sets.Set;

   ----------------------------------------------------------------------
   --  Debug flags
   ----------------------------------------------------------------------

   Debug_Print_Info_Sets_Read : constant Boolean := False;
   --  Enables printing of Subprogram_Info_List as read from ALI files

   Debug_Print_Global_Graph   : constant Boolean := True;
   --  Enables printing of the Global_Graph

   Debug_GG_Read_Timing       : constant Boolean := False;
   --  Enables timing information for gg_read

   ----------------------------------------------------------------------
   --  Local state
   ----------------------------------------------------------------------

   Subprogram_Info_List : Subprogram_Info_Lists.List;
   --  Information about subprograms from the "generated globals" algorithm

   GG_Exists_Cache : Name_Sets.Set;
   --  This should be the equivalent of:
   --     {x.name for all x of Subprogram_Info_List}

   Nonblocking_Subprograms_Set : Name_Sets.Set := Name_Sets.Empty_Set;
   --  Subprograms, entries and tasks that do not contain potentially
   --  blocking statements (but still may call another blocking
   --  subprogram).

   package State_Info_Maps is new Ada.Containers.Hashed_Maps
     (Key_Type        => Entity_Name,
      Element_Type    => Name_Sets.Set,
      Hash            => Name_Hash,
      Equivalent_Keys => "=",
      "="             => Name_Sets."=");
   use State_Info_Maps;

   State_Comp_Map : State_Info_Maps.Map := State_Info_Maps.Empty_Map;
   --  state -> {components}

   Comp_State_Map : Name_Maps.Map       := Name_Maps.Empty_Map;
   --  component -> state
   --
   --  this is filled in at the end of GG_Read from state_comp_map, in order
   --  to speed up some queries

   All_Volatile_Vars     : Name_Sets.Set := Name_Sets.Empty_Set;
   Async_Writers_Vars    : Name_Sets.Set := Name_Sets.Empty_Set;
   Async_Readers_Vars    : Name_Sets.Set := Name_Sets.Empty_Set;
   Effective_Reads_Vars  : Name_Sets.Set := Name_Sets.Empty_Set;
   Effective_Writes_Vars : Name_Sets.Set := Name_Sets.Empty_Set;
   --  Volatile information

   ----------------------------------------------------------------------
   --  Global_Id
   ----------------------------------------------------------------------

   type Global_Id_Kind is (Null_Kind,
                           --  Does not represent anything yet

                           Subprogram_Kind,
                           --  This kind should only be used in Local_Graphs

                           Ins_Kind,
                           --  Represents subprogram's Ins

                           Outs_Kind,
                           --  Represents subprogram's Outs

                           Proof_Ins_Kind,
                           --  Represents subprogram's Proof_Ins

                           Variable_Kind
                           --  Represents a global variable
                          );

   type Global_Id (Kind : Global_Id_Kind := Null_Kind) is record
      case Kind is
         when Null_Kind =>
            null;

         when others =>
            Name : Entity_Name;
      end case;
   end record;

   Null_Global_Id : constant Global_Id := Global_Id'(Kind => Null_Kind);

   function Global_Hash (X : Global_Id) return Ada.Containers.Hash_Type
   is (if X.Kind = Null_Kind
       then Generic_Integer_Hash (-1)
       else Name_Hash (X.Name));

   -------------------
   -- Global_Graphs --
   -------------------

   package Global_Graphs is new Graph (Vertex_Key   => Global_Id,
                                       Key_Hash     => Global_Hash,
                                       Edge_Colours => Edge_Colours,
                                       Null_Key     => Null_Global_Id,
                                       Test_Key     => "=");

   package Vertex_Sets is new Ada.Containers.Hashed_Sets
     (Element_Type        => Global_Graphs.Vertex_Id,
      Hash                => Global_Graphs.Vertex_Hash,
      Equivalent_Elements => Global_Graphs."=",
      "="                 => Global_Graphs."=");

   Local_Graph  : Global_Graphs.T;
   --  This graph will represent the hierarchy of subprograms (which subprogram
   --  is nested in which one) and will be used to determine which local
   --  variables can act as globals to which subprograms.

   Global_Graph : Global_Graphs.T;
   --  This graph will represent the globals that each subprogram has as
   --  inputs, outputs and proof inputs.

   use Global_Graphs;

   -----------------------
   -- Local subprograms --
   -----------------------

   procedure Print_Subprogram_Phase_1_Info (Info : Subprogram_Phase_1_Info);
   --  Prints all info related to a subprogram

   procedure Print_Global_Graph (Filename : String;
                                 G        : T);
   --  Writes dot and pdf files for the Global_Graph

   procedure Add_To_Volatile_Sets_If_Volatile (F : Flow_Id);
   --  Processes F and adds it to All_Volatile_Vars, Async_Writers_Vars,
   --  Async_Readers_Vars, Effective_Reads_Vars, or Effective_Writes_Vars
   --  as appropriate

   --------------------------------------
   -- Add_To_Volatile_Sets_If_Volatile --
   --------------------------------------

   procedure Add_To_Volatile_Sets_If_Volatile (F : Flow_Id)
   is
      N : Entity_Name;
   begin
      case F.Kind is
         when Direct_Mapping | Record_Field =>
            N := To_Entity_Name (Get_Direct_Mapping_Id (F));
         when others =>
            return;
      end case;

      if Is_Volatile (F) then
         All_Volatile_Vars.Include (N);

         if Has_Async_Readers (F) then
            Async_Readers_Vars.Include (N);

            if Has_Effective_Writes (F) then
               Effective_Writes_Vars.Include (N);
            end if;
         end if;

         if Has_Async_Writers (F) then
            Async_Writers_Vars.Include (N);

            if Has_Effective_Reads (F) then
               Effective_Reads_Vars.Include (N);
            end if;
         end if;
      end if;
   end Add_To_Volatile_Sets_If_Volatile;

   -----------------
   -- To_Name_Set --
   -----------------

   function To_Name_Set (S : Node_Sets.Set) return Name_Sets.Set is
   begin
      return X : Name_Sets.Set := Name_Sets.Empty_Set do
         for E of S loop
            X.Insert (To_Entity_Name (E));
         end loop;
      end return;
   end To_Name_Set;

   -----------------------------------
   -- Print_Subprogram_Phase_1_Info --
   -----------------------------------

   procedure Print_Subprogram_Phase_1_Info (Info : Subprogram_Phase_1_Info)
   is
      procedure Write_Name_Set (Header : String; Set : Name_Sets.Set);
      --  Write Header followed by elements of Set

      --------------------
      -- Write_Name_Set --
      --------------------

      procedure Write_Name_Set (Header : String; Set : Name_Sets.Set) is
      begin
         Write_Line (Header);
         for Name of Set loop
            Write_Line ("   " & To_String (Name));
         end loop;
      end Write_Name_Set;

   --  Start of processing for Print_Subprogram_Phase_1_Info

   begin
      Write_Line ((case Info.Kind is
                     when S_Kind => "Subprogram ",
                     when T_Kind => "Task ",
                     when E_Kind => "Entry ") & To_String (Info.Name));

      Write_Name_Set ("Proof_Ins        :", Info.Inputs_Proof);
      Write_Name_Set ("Inputs           :", Info.Inputs);
      Write_Name_Set ("Outputs          :", Info.Outputs);
      Write_Name_Set ("Proof calls      :", Info.Proof_Calls);
      Write_Name_Set ("Definite calls   :", Info.Definite_Calls);
      Write_Name_Set ("Conditional calls:", Info.Conditional_Calls);
      Write_Name_Set ("Local variables  :", Info.Local_Variables);

   end Print_Subprogram_Phase_1_Info;

   ------------------------
   -- Print_Global_Graph --
   ------------------------

   procedure Print_Global_Graph (Filename : String;
                                 G        : T)
   is
      function NDI
        (G : T'Class;
         V : Vertex_Id) return Node_Display_Info;
      --  Pretty-printing for each vertex in the dot output

      function EDI
        (G      : T'Class;
         A      : Vertex_Id;
         B      : Vertex_Id;
         Marked : Boolean;
         Colour : Edge_Colours) return Edge_Display_Info;
      --  Pretty-printing for each edge in the dot output

      ---------
      -- NDI --
      ---------

      function NDI
        (G : T'Class;
         V : Vertex_Id) return Node_Display_Info
      is
         G_Id  : constant Global_Id := G.Get_Key (V);

         Shape : constant Node_Shape_T := (if G_Id.Kind = Variable_Kind
                                           then Shape_Oval
                                           else Shape_Box);

         Label : constant String :=
           (case G_Id.Kind is
              when Subprogram_Kind => "Subprogram " & To_String (G_Id.Name),
              when Proof_Ins_Kind  => To_String (G_Id.Name) & "'Proof_Ins",
              when Ins_Kind        => To_String (G_Id.Name) & "'Ins",
              when Outs_Kind       => To_String (G_Id.Name) & "'Outs",
              when Variable_Kind   => To_String (G_Id.Name),
              when Null_Kind       => "");

         Rv : constant Node_Display_Info := Node_Display_Info'
           (Show        => True,
            Shape       => Shape,
            Colour      => Null_Unbounded_String,
            Fill_Colour => Null_Unbounded_String,
            Label       => To_Unbounded_String (Label));
      begin
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
         pragma Unreferenced (G, A, B, Marked, Colour);

         Rv : constant Edge_Display_Info :=
           Edge_Display_Info'(Show   => True,
                              Shape  => Edge_Normal,
                              Colour => Null_Unbounded_String,
                              Label  => Null_Unbounded_String);
      begin
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
   end Print_Global_Graph;

   -------------------------
   -- GG_Write_Initialize --
   -------------------------

   procedure GG_Write_Initialize is
   begin
      Open_Output_Library_Info;

      --  Initialze subprogram info
      Subprogram_Info_List        := Subprogram_Info_Lists.Empty_List;
      GG_Exists_Cache             := Name_Sets.Empty_Set;

      --  Initialize state info
      State_Comp_Map              := State_Info_Maps.Empty_Map;

      --  Initialize volatile info
      All_Volatile_Vars           := Name_Sets.Empty_Set;
      Async_Writers_Vars          := Name_Sets.Empty_Set;
      Async_Readers_Vars          := Name_Sets.Empty_Set;
      Effective_Reads_Vars        := Name_Sets.Empty_Set;
      Effective_Writes_Vars       := Name_Sets.Empty_Set;

      --  Set mode to writing mode
      Current_Mode                := GG_Write_Mode;
   end GG_Write_Initialize;

   ---------------------------
   -- GG_Write_Package_Info --
   ---------------------------

   procedure GG_Write_Package_Info (DM : Dependency_Maps.Map) is
   begin
      for S in DM.Iterate loop
         declare
            State_F      : constant Flow_Id := Dependency_Maps.Key (S);

            State_N      : constant Entity_Name :=
              To_Entity_Name (Get_Direct_Mapping_Id (State_F));

            Constituents : constant Name_Sets.Set :=
              To_Name_Set (To_Node_Set (Dependency_Maps.Element (S)));
         begin
            --  Insert new state info into State_Comp_Map.
            State_Comp_Map.Insert (State_N, Constituents);

            --  Check if State_F if volatile and if it is then add it on
            --  the appropriate sets.
            Add_To_Volatile_Sets_If_Volatile (State_F);
         end;
      end loop;
   end GG_Write_Package_Info;

   ------------------------------
   -- GG_Write_Subprogram_Info --
   ------------------------------

   procedure GG_Write_Subprogram_Info (SI : Subprogram_Phase_1_Info) is
      procedure Process_Volatiles (S : Name_Sets.Set);
      --  Goes through S, finds volatiles and stores them in the
      --  appropriate sets based on their properties.

      ------------------------
      -- Processs_Volatiles --
      ------------------------

      procedure Process_Volatiles (S : Name_Sets.Set) is
      begin
         for Name of S loop
            declare
               E : constant Entity_Id := Find_Entity (Name);
            begin
               if Present (E) then
                  Add_To_Volatile_Sets_If_Volatile (Direct_Mapping_Id (E));
               end if;
            end;
         end loop;
      end Process_Volatiles;

   begin
      Subprogram_Info_List.Append (SI);
      GG_Exists_Cache.Insert (SI.Name);

      --  Gather and save volatile variables
      Process_Volatiles (SI.Inputs_Proof);
      Process_Volatiles (SI.Inputs);
      Process_Volatiles (SI.Outputs);
      Process_Volatiles (SI.Local_Variables);
   end GG_Write_Subprogram_Info;

   -----------------------------
   -- GG_Register_Nonblocking --
   -----------------------------

   procedure GG_Register_Nonblocking (EN : Entity_Name)
   is
   begin
      Nonblocking_Subprograms_Set.Insert (EN);
   end GG_Register_Nonblocking;

   -----------------------
   -- GG_Write_Finalize --
   -----------------------

   procedure GG_Write_Finalize is
      procedure Write_Name_Set (Tag : String; S : Name_Sets.Set);

      --------------------
      -- Write_Name_Set --
      --------------------

      procedure Write_Name_Set (Tag : String; S : Name_Sets.Set) is
      begin
         Write_Info_Str (Tag);
         for N of S loop
            Write_Info_Char (' ');
            Write_Info_Str (To_String (N));
         end loop;
         Write_Info_Terminate;
      end Write_Name_Set;

   --  Start of processing for GG_Write_Finalize

   begin
      --  Write State info
      for C in State_Comp_Map.Iterate loop
         declare
            State        : constant Entity_Name   := Key (C);
            Constituents : constant Name_Sets.Set := Element (C);
         begin
            Write_Name_Set ("GG AS " & To_String (State),
                            Constituents);
         end;
      end loop;

      --  Write Subprogram/Task/Entry info
      for Info of Subprogram_Info_List loop
         Write_Name_Set ((case Info.Kind is
                             when S_Kind => "GG S ",
                             when T_Kind => "GG T ",
                             when E_Kind => "GG E ") &
                         (case Info.Globals_Origin is
                             when UG => "UG ",
                             when FA => "FA ",
                             when XR => "XR ") &
                         To_String (Info.Name),
                         Name_Sets.Empty_Set);

         Write_Name_Set ("GG VP", Info.Inputs_Proof);
         Write_Name_Set ("GG VI", Info.Inputs);
         Write_Name_Set ("GG VO", Info.Outputs);
         Write_Name_Set ("GG CP", Info.Proof_Calls);
         Write_Name_Set ("GG CD", Info.Definite_Calls);
         Write_Name_Set ("GG CC", Info.Conditional_Calls);
         Write_Name_Set ("GG LV", Info.Local_Variables);
         Write_Name_Set ("GG LS", Info.Local_Subprograms);
      end loop;

      --  Write Volatile info

      --  Write Async_Writers
      if not Async_Writers_Vars.Is_Empty then
         Write_Name_Set ("GG AW", Async_Writers_Vars);
      end if;

      --  Write Async_Readers
      if not Async_Readers_Vars.Is_Empty then
         Write_Name_Set ("GG AR", Async_Readers_Vars);
      end if;

      --  Write Effective_Reads
      if not Effective_Reads_Vars.Is_Empty then
         Write_Name_Set ("GG ER", Effective_Reads_Vars);
      end if;

      --  Write Effective_Writes
      if not Effective_Writes_Vars.Is_Empty then
         Write_Name_Set ("GG EW", Effective_Writes_Vars);
      end if;

      --  Write nonblocking subprograms
      if not Nonblocking_Subprograms_Set.Is_Empty then
         Write_Name_Set ("GG NB", Nonblocking_Subprograms_Set);
      end if;

      Close_Output_Library_Info;
      Current_Mode := GG_No_Mode;
   end GG_Write_Finalize;

   -------------
   -- GG_Read --
   -------------

   procedure GG_Read (GNAT_Root : Node_Id) is
      All_Globals           : Name_Sets.Set := Name_Sets.Empty_Set;
      --  Contains all global variables

      GG_Subprograms        : Name_Sets.Set := Name_Sets.Empty_Set;
      --  Contains all subprograms for which a GG entry exists

      All_Subprograms       : Name_Sets.Set := Name_Sets.Empty_Set;
      --  Contains all subprograms that we know of, even if a
      --  GG entry does not exist for them.

      All_Other_Subprograms : Name_Sets.Set := Name_Sets.Empty_Set;
      --  Contains all subprograms for which a GG entry does not exist

      procedure Add_All_Edges;
      --  Reads the populated Subprogram_Info_List and generates all the edges
      --  of the Global_Graph. While adding edges we consult the Local_Graph so
      --  as not to add edges to local variables.

      procedure Create_All_Vertices;
      --  Creates all the vertices of the Global_Graph

      procedure Create_Local_Graph;
      --  Creates the Local_Graph. This graph will be used to prevent adding
      --  edges to local variables on the Global_Graph.

      procedure Edit_Proof_Ins;
      --  A variable cannot be simultaneously a Proof_In and an Input
      --  of a subprogram. In this case we need to remove the Proof_In
      --  edge. Furthermore, a variable cannot be simultaneously a
      --  Proof_In and an Output (but not an input). In this case we
      --  need to change the Proof_In variable into an Input.

      procedure Load_GG_Info_From_ALI (ALI_File_Name : File_Name_Type);
      --  Loads the GG info from an ALI file and stores them in the
      --  Subprogram_Info_List, State_Comp_Map and volatile info sets.
      --
      --  The info that we read look as follows:
      --
      --  GG AS test__state test__g
      --  GG S FA test__proc
      --  GG VP test__proof_var
      --  GG VI test__g test__g2
      --  GG VO test__g
      --  GG CP test__ghost_func_a test__ghost_func_b
      --  GG CD test__proc_2 test__proc__nested_proc
      --  GG CC test__proc_3
      --  GG LV test__proc__nested_proc__v
      --  GG LS test__proc__nested_proc
      --  GG AW test__fully_vol test__vol_er2 test__ext_state
      --  GG AR test__fully_vol test__vol_ew3
      --  GG ER test__fully_vol test__vol_er2
      --  GG EW test__fully_vol test__vol_ew3
      --  GG NB test__proc

      procedure Remove_Constants_Without_Variable_Input;
      --  Removes edges leading to constants without variable input

      -------------------
      -- Add_All_Edges --
      -------------------

      procedure Add_All_Edges is
         G_Ins, G_Outs, G_Proof_Ins : Global_Id;

         procedure Add_Edge (G1, G2 : Global_Id);
         --  Adds an edge between the vertices V1 and V2 that
         --  correspond to G1 and G2 (V1 --> V2). The edge has the
         --  default colour.

         function Edge_Selector (A, B : Vertex_Id) return Boolean;
         --  Check if we should add the given edge to the graph based
         --  wheather it is in the local graph or not.

         --------------
         -- Add_Edge --
         --------------

         procedure Add_Edge (G1, G2 : Global_Id) is
         begin
            Global_Graph.Add_Edge (G1, G2, EC_Default);
         end Add_Edge;

         -------------------
         -- Edge_Selector --
         -------------------

         function Edge_Selector (A, B : Vertex_Id) return Boolean is
            Key_A :          Global_Id := Global_Graph.Get_Key (A);
            Key_B : constant Global_Id := Global_Graph.Get_Key (B);
         begin
            if Key_B.Kind /= Variable_Kind
              or else not (Key_A.Kind in Proof_Ins_Kind |
                             Ins_Kind       |
                             Outs_Kind)
            then
               --  We only need to consult the Local_Graph when attempting
               --  to establish a link between a subprogram and a variable.
               return True;
            end if;

            --  Convert kind so that it can be used on Local_Graph
            Key_A := Global_Id'(Kind => Subprogram_Kind,
                                Name => Key_A.Name);

            if Local_Graph.Get_Vertex (Key_A) = Null_Vertex
              or else Local_Graph.Get_Vertex (Key_B) = Null_Vertex
            then
               return True;
            end if;

            --  Check if local variable B can act as global of subprogram A
            return Local_Graph.Edge_Exists (Key_B, Key_A);
         end Edge_Selector;

      begin

         --  Go through the Subprogram_Info_List and add edges
         for Info of Subprogram_Info_List loop
            G_Ins       := Global_Id'(Kind => Ins_Kind,
                                      Name => Info.Name);

            G_Outs      := Global_Id'(Kind => Outs_Kind,
                                      Name => Info.Name);

            G_Proof_Ins := Global_Id'(Kind => Proof_Ins_Kind,
                                      Name => Info.Name);

            --  Connecting the subprogram's Proof_In variables to the
            --  subprogram's Proof_Ins vertex.
            for Input_Proof of Info.Inputs_Proof loop
               Add_Edge (G_Proof_Ins,
                         Global_Id'(Kind => Variable_Kind,
                                    Name => Input_Proof));
            end loop;

            --  Connecting the subprogram's Input variables to the
            --  subprogram's Ins vertex.
            for Input of Info.Inputs loop
               Add_Edge (G_Ins,
                         Global_Id'(Kind => Variable_Kind,
                                    Name => Input));
            end loop;

            --  Connecting the subprogram's Output variables to the
            --  subprogram's Outputs vertex.
            for Output of Info.Outputs loop
               Add_Edge (G_Outs,
                         Global_Id'(Kind => Variable_Kind,
                                    Name => Output));
            end loop;

            --  Connecting the subprogram's Proof_Ins vertex to the
            --  callee's Ins and Proof_Ins vertices.
            for Proof_Call of Info.Proof_Calls loop
               Add_Edge (G_Proof_Ins,
                         Global_Id'(Kind => Proof_Ins_Kind,
                                    Name => Proof_Call));

               Add_Edge (G_Proof_Ins,
                         Global_Id'(Kind => Ins_Kind,
                                    Name => Proof_Call));
            end loop;

            --  Connecting the subprogram's Proof_Ins, Ins and Outs
            --  vertices respectively to the callee's Proof_Ins, Ins
            --  and Outs vertices.
            for Definite_Call of Info.Definite_Calls loop
               Add_Edge (G_Proof_Ins,
                         Global_Id'(Kind => Proof_Ins_Kind,
                                    Name => Definite_Call));

               Add_Edge (G_Ins,
                         Global_Id'(Kind => Ins_Kind,
                                    Name => Definite_Call));

               Add_Edge (G_Outs,
                         Global_Id'(Kind => Outs_Kind,
                                    Name => Definite_Call));
            end loop;

            --  As above but we also add an edge from the subprogram's
            --  Ins vertex to the callee's Outs vertex.
            for Conditional_Call of Info.Conditional_Calls loop
               Add_Edge (G_Proof_Ins,
                         Global_Id'(Kind => Proof_Ins_Kind,
                                    Name => Conditional_Call));

               Add_Edge (G_Ins,
                         Global_Id'(Kind => Ins_Kind,
                                    Name => Conditional_Call));

               Add_Edge (G_Ins,
                         Global_Id'(Kind => Outs_Kind,
                                    Name => Conditional_Call));

               Add_Edge (G_Outs,
                         Global_Id'(Kind => Outs_Kind,
                                    Name => Conditional_Call));
            end loop;
         end loop;

         --  Add edges between subprograms and variables coming from
         --  the Get_Globals function.
         for N of All_Other_Subprograms loop
            declare
               Subprogram   : constant Entity_Id := Find_Entity (N);
               G_Proof_Ins  : Global_Id;
               G_Ins        : Global_Id;
               G_Outs       : Global_Id;
               FS_Proof_Ins : Flow_Id_Sets.Set;
               FS_Reads     : Flow_Id_Sets.Set;
               FS_Writes    : Flow_Id_Sets.Set;

               procedure Add_Edges_For_FS
                 (FS   : Flow_Id_Sets.Set;
                  From : Global_Id);
               --  Adds an edge from From to every Flow_Id in FS

               ----------------------
               -- Add_Edges_For_FS --
               ----------------------

               procedure Add_Edges_For_FS
                 (FS   : Flow_Id_Sets.Set;
                  From : Global_Id)
               is
                  G   : Global_Id;
                  Nam : Entity_Name;
               begin
                  for F of FS loop
                     Nam := (if F.Kind in Direct_Mapping |
                                          Record_Field
                             then
                                To_Entity_Name (Get_Direct_Mapping_Id (F))
                             elsif F.Kind = Magic_String then
                                F.Name
                             else
                                raise Program_Error);
                     G   := Global_Id'(Kind => Variable_Kind,
                                       Name => Nam);

                     if not Global_Graph.Edge_Exists (From, G) then
                        Add_Edge (From, G);
                     end if;
                  end loop;
               end Add_Edges_For_FS;

            begin
               G_Proof_Ins := Global_Id'(Kind => Proof_Ins_Kind,
                                         Name => N);

               G_Ins       := Global_Id'(Kind => Ins_Kind,
                                         Name => N);

               G_Outs      := Global_Id'(Kind => Outs_Kind,
                                         Name => N);

               if Subprogram /= Empty then
                  Get_Globals (Subprogram => Subprogram,
                               Scope      => Get_Flow_Scope (Subprogram),
                               Classwide  => False,
                               Proof_Ins  => FS_Proof_Ins,
                               Reads      => FS_Reads,
                               Writes     => FS_Writes);

                  Add_Edges_For_FS (FS_Proof_Ins, G_Proof_Ins);
                  Add_Edges_For_FS (FS_Reads, G_Ins);
                  Add_Edges_For_FS (FS_Writes, G_Outs);
               end if;
            end;
         end loop;

         --  Close graph, but only add edges that are not in the local
         --  graph.
         Global_Graph.Conditional_Close (Edge_Selector'Access);
      end Add_All_Edges;

      -------------------------
      -- Create_All_Vertices --
      -------------------------

      procedure Create_All_Vertices is
      begin
         --  Create vertices for all global variables
         for N of All_Globals loop
            Global_Graph.Add_Vertex (Global_Id'(Kind => Variable_Kind,
                                                Name => N));
         end loop;

         --  Create Ins, Outs and Proof_Ins vertices for all subprograms
         for N of All_Subprograms loop
            declare
               G_Ins       : constant Global_Id :=
                 Global_Id'(Kind => Ins_Kind,
                            Name => N);

               G_Outs      : constant Global_Id :=
                 Global_Id'(Kind => Outs_Kind,
                            Name => N);

               G_Proof_Ins : constant Global_Id :=
                 Global_Id'(Kind => Proof_Ins_Kind,
                            Name => N);
            begin
               Global_Graph.Add_Vertex (G_Ins);
               Global_Graph.Add_Vertex (G_Outs);
               Global_Graph.Add_Vertex (G_Proof_Ins);
            end;
         end loop;

         --  Lastly, create vertices for variables that come from the
         --  Get_Globals function.
         for N of All_Other_Subprograms loop
            declare
               Subprogram   : constant Entity_Id := Find_Entity (N);
               FS_Proof_Ins : Flow_Id_Sets.Set;
               FS_Reads     : Flow_Id_Sets.Set;
               FS_Writes    : Flow_Id_Sets.Set;

               procedure Create_Vertices_For_FS (FS : Flow_Id_Sets.Set);
               --  Creates a vertex for every Flow_Id in FS that
               --  does not already have one.

               ----------------------------
               -- Create_Vertices_For_FS --
               ----------------------------

               procedure Create_Vertices_For_FS (FS : Flow_Id_Sets.Set) is
                  G   : Global_Id;
                  Nam : Entity_Name;
               begin
                  for F of FS loop
                     Nam := (if F.Kind in Direct_Mapping | Record_Field then
                                To_Entity_Name (Get_Direct_Mapping_Id (F))
                             elsif F.Kind = Magic_String then
                                F.Name
                             else
                                raise Program_Error);
                     G   := Global_Id'(Kind => Variable_Kind,
                                       Name => Nam);

                     if Global_Graph.Get_Vertex (G) = Null_Vertex then
                        Global_Graph.Add_Vertex (G);
                     end if;
                  end loop;
               end Create_Vertices_For_FS;

            begin
               if Subprogram /= Empty then
                  Get_Globals (Subprogram => Subprogram,
                               Scope      => Get_Flow_Scope (Subprogram),
                               Classwide  => False,
                               Proof_Ins  => FS_Proof_Ins,
                               Reads      => FS_Reads,
                               Writes     => FS_Writes);

                  Create_Vertices_For_FS (FS_Proof_Ins);
                  Create_Vertices_For_FS (FS_Reads);
                  Create_Vertices_For_FS (FS_Writes);
               end if;
            end;
         end loop;
      end Create_All_Vertices;

      ------------------------
      -- Create_Local_Graph --
      ------------------------

      procedure Create_Local_Graph is

         procedure Add_Edge (G1, G2 : Global_Id);
         --  Adds an edge between the vertices V1 and V2 that correspond to G1
         --  and G2 (V1 --> V2). The edge has the default colour. This
         --  procedure operates on the Local_Graph.

         --------------
         -- Add_Edge --
         --------------

         procedure Add_Edge (G1, G2 : Global_Id) is
         begin
            Local_Graph.Add_Edge (G1, G2, EC_Default);
         end Add_Edge;

         G_Subp       : Global_Id;
         G_Local_Subp : Global_Id;
         G_Local_Var  : Global_Id;

      --  Start of processing for Create_Local_Graph

      begin
         for Info of Subprogram_Info_List loop
            G_Subp := Global_Id'(Kind => Subprogram_Kind,
                                 Name => Info.Name);

            if Local_Graph.Get_Vertex (G_Subp) = Null_Vertex then
               --  Create a vertex for the subprogram if one does not already
               --  exist.
               Local_Graph.Add_Vertex (G_Subp);
            end if;

            --  Create a vertex for every local variable and link it to the
            --  enclosing subprogram.
            for Local_Variable of Info.Local_Variables loop
               G_Local_Var := Global_Id'(Kind => Variable_Kind,
                                         Name => Local_Variable);

               --  Create a vertex for every local variable if one does not
               --  already exist.
               if Local_Graph.Get_Vertex (G_Local_Var) = Null_Vertex then
                  Local_Graph.Add_Vertex (G_Local_Var);
               end if;

               --  Link enclosing subprogram to local variable
               Add_Edge (G_Subp, G_Local_Var);
            end loop;

            --  Create a vertex for every local subprogram and link it to the
            --  enclosing subprogram.
            for Local_Subprogram of Info.Local_Subprograms loop
               G_Local_Subp := Global_Id'(Kind => Subprogram_Kind,
                                          Name => Local_Subprogram);

               if Local_Graph.Get_Vertex (G_Local_Subp) = Null_Vertex then
                  --  Create a vertex for every local subprogram if one does
                  --  not already exist.
                  Local_Graph.Add_Vertex (G_Local_Subp);
               end if;

               --  Link enclosing subprogram to local subprogram
               Add_Edge (G_Subp, G_Local_Subp);
            end loop;

            --  Link all local variables to all local subprograms (this
            --  effectively means that they can act as their globals).
            for Local_Variable of Info.Local_Variables loop
               G_Local_Var := Global_Id'(Kind => Variable_Kind,
                                         Name => Local_Variable);

               for Local_Subprogram of Info.Local_Subprograms loop
                  G_Local_Subp := Global_Id'(Kind => Subprogram_Kind,
                                             Name => Local_Subprogram);

                  Add_Edge (G_Local_Var, G_Local_Subp);
               end loop;
            end loop;
         end loop;

         --  Close graph
         Local_Graph.Close;
      end Create_Local_Graph;

      --------------------
      -- Edit_Proof_Ins --
      --------------------

      procedure Edit_Proof_Ins is
         function Get_Variable_Neighbours
           (Start : Vertex_Id)
            return Vertex_Sets.Set;
         --  Returns a set of all Neighbours of Start that correspond
         --  to variables.

         -----------------------------
         -- Get_Variable_Neighbours --
         -----------------------------

         function Get_Variable_Neighbours
           (Start : Vertex_Id)
            return Vertex_Sets.Set
         is
            VS : Vertex_Sets.Set := Vertex_Sets.Empty_Set;
         begin
            for V of Global_Graph.Get_Collection (Start,
                                                  Out_Neighbours)
            loop
               if Global_Graph.Get_Key (V).Kind = Variable_Kind then
                  VS.Include (V);
               end if;
            end loop;

            return VS;
         end Get_Variable_Neighbours;

      --  Start of processing for Edit_Proof_Ins

      begin
         for Info of Subprogram_Info_List loop
            declare
               G_Ins       : constant Global_Id :=
                 Global_Id'(Kind => Ins_Kind,
                            Name => Info.Name);

               G_Outs      : constant Global_Id :=
                 Global_Id'(Kind => Outs_Kind,
                            Name => Info.Name);

               G_Proof_Ins : constant Global_Id :=
                 Global_Id'(Kind => Proof_Ins_Kind,
                            Name => Info.Name);

               V_Ins       : constant Vertex_Id :=
                 Global_Graph.Get_Vertex (G_Ins);

               V_Outs      : constant Vertex_Id :=
                 Global_Graph.Get_Vertex (G_Outs);

               V_Proof_Ins : constant Vertex_Id :=
                 Global_Graph.Get_Vertex (G_Proof_Ins);

               Inputs      : constant Vertex_Sets.Set :=
                 Get_Variable_Neighbours (V_Ins);

               Outputs     : constant Vertex_Sets.Set :=
                 Get_Variable_Neighbours (V_Outs);

               Proof_Ins   : constant Vertex_Sets.Set :=
                 Get_Variable_Neighbours (V_Proof_Ins);
            begin
               for V of Proof_Ins loop
                  if Inputs.Contains (V)
                    or else Outputs.Contains (V)
                  then
                     if not Global_Graph.Edge_Exists (V_Ins, V) then
                        Global_Graph.Add_Edge (V_Ins, V, EC_Default);
                     end if;

                     Global_Graph.Remove_Edge (V_Proof_Ins, V);
                  end if;
               end loop;
            end;
         end loop;
      end Edit_Proof_Ins;

      ---------------------------
      -- Load_GG_Info_From_ALI --
      ---------------------------

      procedure Load_GG_Info_From_ALI (ALI_File_Name : File_Name_Type) is
         ALI_File_Name_Str : constant String :=
           Name_String (Name_Id (Full_Lib_File_Name (ALI_File_Name)));

         ALI_File : Ada.Text_IO.File_Type;
         Line     : Unbounded_String;

         type External_State is
           (Async_Readers,
            Async_Writers,
            Effective_Reads,
            Effective_Writes
           );

         External_State_Found : array (External_State) of Boolean :=
           (others => False);

         type GG_Tag is array (Positive range 1 .. 2) of Character;

         External_State_Tags : constant array (External_State) of GG_Tag :=
           (Async_Readers    => "AR",
            Async_Writers    => "AW",
            Effective_Reads  => "ER",
            Effective_Writes => "EW"
           );

         procedure Parse_Record;
         --  Parses a GG record from the ALI file and if no problems
         --  occurred adds it to the relevant set.

         ------------------
         -- Parse_Record --
         ------------------

         procedure Parse_Record is

            type Line_Index is range 1 .. 9;

            type Line_Found_T is array (Line_Index) of Boolean;
            --  This array represents whether we have found a line
            --  of the following format while populating the record.
            --  The order is as follow:
            --
            --  array slot 1 is True if we have found "GG S/T/E *"
            --  array slot 2 is True if we have found "GG VP *"
            --  array slot 3 is True if we have found "GG VI *"
            --  array slot 4 is True if we have found "GG VO *"
            --  array slot 5 is True if we have found "GG CP *"
            --  array slot 6 is True if we have found "GG CD *"
            --  array slot 7 is True if we have found "GG CC *"
            --  array slot 8 is True if we have found "GG LV *"
            --  array slot 9 is True if we have found "GG LS *"

            Line_Found : Line_Found_T := Line_Found_T'(others => False);
            --  Initially we haven't found anything

            New_Info   : Subprogram_Phase_1_Info;

            procedure Check_GG_Format;
            --  Checks if the line start with "GG "

            function Get_Names_From_Line return Name_Sets.Set;
            --  Returns a set of all names appearing in a line

            procedure Set_Line_Found (L : Line_Index);
            --  Set Line_Found (L) to True or raise an exception if it is
            --  already set.

            ---------------------
            -- Check_GG_Format --
            ---------------------

            procedure Check_GG_Format is
            begin
               if Length (Line) <= 3 or else
                 Slice (Line, 1, 3) /= "GG "
               then
                  --  Either the ALI file has been tampered with
                  --  or we are dealing with a new kind of line
                  --  that we are not aware of.
                  raise Program_Error;
               end if;
            end Check_GG_Format;

            -------------------------
            -- Get_Names_From_Line --
            -------------------------

            function Get_Names_From_Line return Name_Sets.Set is
               Names_In_Line : Name_Sets.Set := Name_Sets.Empty_Set;
               Start_Of_Word : Natural       := 7;
               End_Of_Word   : Natural;
            begin
               if Length (Line) = 5 then
                  --  There are no names here. Return the empty set.
                  return Names_In_Line;
               end if;

               while Start_Of_Word < Length (Line) loop
                  End_Of_Word := Start_Of_Word;

                  while End_Of_Word < Length (Line)
                    and then Element (Line, End_Of_Word) > ' '
                  loop
                     End_Of_Word := End_Of_Word + 1;
                  end loop;

                  --  If we have not reached the end of the line then
                  --  we have read one character too many.
                  if End_Of_Word < Length (Line) then
                     End_Of_Word := End_Of_Word - 1;
                  end if;

                  declare
                     EN : constant Entity_Name :=
                       To_Entity_Name (Slice (Line,
                                              Start_Of_Word,
                                              End_Of_Word));
                  begin
                     Names_In_Line.Insert (EN);
                  end;

                  Start_Of_Word := End_Of_Word + 2;
               end loop;

               return Names_In_Line;
            end Get_Names_From_Line;

            --------------------
            -- Set_Line_Found --
            --------------------

            procedure Set_Line_Found (L : Line_Index) is
            begin
               if Line_Found (L) then
                  raise Program_Error;
               else
                  Line_Found (L) := True;
               end if;
            end Set_Line_Found;

         --  Start of processing for Parse_Record

         begin
            --  We special case lines that contain info about state
            --  abstractions.
            if Length (Line) > 6
              and then Slice (Line, 1, 6) = "GG AS "
            then
               declare
                  State         : Entity_Name;
                  Constituents  : Name_Sets.Set := Get_Names_From_Line;
                  Start_Of_Word : constant Natural := 7;
                  End_Of_Word   : Natural := 7;
               begin
                  while End_Of_Word < Length (Line)
                    and then Element (Line, End_Of_Word) > ' '
                  loop
                     End_Of_Word := End_Of_Word + 1;
                  end loop;

                  --  If we have not reached the end of the line then
                  --  we have read one character too many.
                  if End_Of_Word < Length (Line) then
                     End_Of_Word := End_Of_Word - 1;
                  end if;

                  State := To_Entity_Name (Slice (Line,
                                                  Start_Of_Word,
                                                  End_Of_Word));

                  Constituents.Exclude (State);

                  State_Comp_Map.Include (State, Constituents);
               end;

               --  State line parsed. We will now return.
               return;

            --  We special case lines that contain info about volatile
            --  variables and external state abstractions.

            elsif Length (Line) > 6
              and then Element (Line, 4) in 'A' | 'E'
              and then Element (Line, 5) in 'R' | 'W'
              and then Element (Line, 6) = ' '
            then
               declare
                  Names : constant Name_Sets.Set := Get_Names_From_Line;

                  ES_Tag : constant GG_Tag := GG_Tag (Slice (Line, 4, 5));
                  ES : External_State;

               begin
                  for I in External_State'Range loop
                     if ES_Tag = External_State_Tags (I) then
                        ES := I;
                        exit;
                     end if;
                  end loop;

                  --  Check if this tag was not already seen
                  if External_State_Found (ES) then
                     raise Program_Error;
                  else
                     External_State_Found (ES) := True;
                  end if;

                  --  Update the correponding set
                  case ES is
                     when Async_Writers =>
                        Async_Writers_Vars.Union (Names);

                     when Async_Readers =>
                        Async_Readers_Vars.Union (Names);

                     when Effective_Reads =>
                        Effective_Reads_Vars.Union (Names);

                     when Effective_Writes =>
                        Effective_Writes_Vars.Union (Names);
                  end case;

                  --  Store all names from the line in the All_Volatile_Vars
                  --  set and return.
                  All_Volatile_Vars.Union (Get_Names_From_Line);
                  return;
               end;

            elsif Length (Line) > 6
              and then Slice (Line, 1, 6) = "GG NB "
            then

               Nonblocking_Subprograms_Set.Union (Get_Names_From_Line);
               return;

            end if;

            while (for some I in Line_Index => not Line_Found (I)) loop
               Check_GG_Format;

               if Length (Line) >= 6
                 and then Element (Line, 4) in 'S' | 'T' | 'E'
                 and then Element (Line, 5) = ' '
               then
                  --  Line format: GG S *
                  --      or       GG T *
                  --      or       GG E *
                  Set_Line_Found (1);

                  New_Info.Kind := (case Element (Line, 4) is
                                       when 'S' => S_Kind, -- subprogram
                                       when 'T' => T_Kind, -- task
                                       when 'E' => E_Kind, -- entry
                                       when others => raise Program_Error
                                   );

                  declare
                     GO : constant String := Slice (Line, 6, 7);

                     EN : constant Entity_Name :=
                       To_Entity_Name (Slice (Line, 9, Length (Line)));

                  begin
                     New_Info.Name := EN;
                     New_Info.Globals_Origin :=
                       (if GO = "UG" then UG
                        elsif GO = "FA" then FA
                        elsif GO = "XR" then XR
                        else raise Program_Error);
                     GG_Subprograms.Include (EN);
                     All_Subprograms.Include (EN);
                  end;

               elsif Length (Line) >= 5 then
                  declare
                     Tag : constant String := Slice (Line, 4, 5);
                  begin
                     if Tag = "VP" then
                        Set_Line_Found (2);

                        New_Info.Inputs_Proof := Get_Names_From_Line;
                        All_Globals.Union (New_Info.Inputs_Proof);

                     elsif Tag = "VI" then
                        Set_Line_Found (3);

                        New_Info.Inputs := Get_Names_From_Line;
                        All_Globals.Union (New_Info.Inputs);

                     elsif Tag = "VO" then
                        Set_Line_Found (4);

                        New_Info.Outputs := Get_Names_From_Line;
                        All_Globals.Union (New_Info.Outputs);

                     elsif Tag = "CP" then
                        Set_Line_Found (5);

                        New_Info.Proof_Calls := Get_Names_From_Line;
                        All_Subprograms.Union (New_Info.Proof_Calls);

                     elsif Tag = "CD" then
                        Set_Line_Found (6);

                        New_Info.Definite_Calls := Get_Names_From_Line;
                        All_Subprograms.Union (New_Info.Definite_Calls);

                     elsif Tag = "CC" then
                        Set_Line_Found (7);

                        New_Info.Conditional_Calls := Get_Names_From_Line;
                        All_Subprograms.Union (New_Info.Conditional_Calls);

                     elsif Tag = "LV" then
                        Set_Line_Found (8);

                        New_Info.Local_Variables := Get_Names_From_Line;
                        All_Globals.Union (New_Info.Local_Variables);

                     elsif Tag = "LS" then
                        Set_Line_Found (9);

                        New_Info.Local_Subprograms := Get_Names_From_Line;
                        All_Subprograms.Union (New_Info.Local_Subprograms);

                     else
                        --  Unexpected type of line. Something is wrong
                        --  with the ALI file.
                        raise Program_Error;
                     end if;

                  end;

               else
                  --  Something is wrong with the ALI file
                  raise Program_Error;
               end if;

               if not End_Of_File (ALI_File)
                 and then (for some I in Line_Index => not Line_Found (I))
               then
                  --  Go to the next line
                  Get_Line (ALI_File, Line);
               elsif End_Of_File (ALI_File)
                 and then (for some I in Line_Index => not Line_Found (I))
               then
                  --  We reached the end of the file and our New_Info
                  --  is not yet complete. Something is missing from
                  --  the ALI file.
                  raise Program_Error;
               end if;

               if (for all I in Line_Index => Line_Found (I)) then
                  --  If all lines have been found then we add New_Info to
                  --  Subprogram_Info_List and return.
                  Subprogram_Info_List.Append (New_Info);
                  GG_Exists_Cache.Insert (New_Info.Name);
                  return;
               end if;

            end loop;

            --  We should never reach here
            raise Program_Error;

         end Parse_Record;

      --  Start of processing for Load_GG_Info_From_ALI

      begin
         Open (ALI_File, In_File, ALI_File_Name_Str);

         loop
            if End_Of_File (ALI_File) then
               Close (ALI_File);
               return;
            end if;

            Get_Line (ALI_File, Line);

            --  Check if now reached the "GG" section
            if Length (Line) >= 3 and then Slice (Line, 1, 3) = "GG " then
               exit;
            end if;
         end loop;

         --  We have now reached the "GG" section of the ALI file
         Parse_Record;
         while not End_Of_File (ALI_File) loop
            Get_Line (ALI_File, Line);
            Parse_Record;
         end loop;

         Close (ALI_File);
      end Load_GG_Info_From_ALI;

      ---------------------------------------------
      -- Remove_Constants_Without_Variable_Input --
      ---------------------------------------------

      procedure Remove_Constants_Without_Variable_Input is
         All_Constants : Name_Sets.Set  := Name_Sets.Empty_Set;
      begin
         --  Gather up all constants without variable input
         for Glob of All_Globals loop
            declare
               Const : constant Entity_Id := Find_Entity (Glob);
            begin
               if Const /= Empty
                 and then Ekind (Const) = E_Constant
                 and then not Has_Variable_Input (Direct_Mapping_Id (Const))
               then
                  All_Constants.Include (Glob);
               end if;
            end;
         end loop;

         --  Remove all edges going in and out of a constant without
         --  variable input.
         for Const of All_Constants loop
            declare
               Const_G_Id : constant Global_Id :=
                 Global_Id'(Kind => Variable_Kind,
                            Name => Const);

               Const_V    : constant Vertex_Id :=
                 Global_Graph.Get_Vertex (Const_G_Id);
            begin
               Global_Graph.Clear_Vertex (Const_V);
            end;
         end loop;
      end Remove_Constants_Without_Variable_Input;

   --  Start of processing for GG_Read

   begin
      Current_Mode := GG_Read_Mode;

      if Debug_GG_Read_Timing then
         Init_Time ("gg_read");
      end if;

      --  Initialize volatile info
      All_Volatile_Vars     := Name_Sets.Empty_Set;
      Async_Writers_Vars    := Name_Sets.Empty_Set;
      Async_Readers_Vars    := Name_Sets.Empty_Set;
      Effective_Reads_Vars  := Name_Sets.Empty_Set;
      Effective_Writes_Vars := Name_Sets.Empty_Set;

      --  Go through all ALI files and populate the Subprogram_Info_List.
      declare
         Read_Files : Unbounded_String_Sets.Set;
         Nam        : Unbounded_String;
      begin
         Read_Files := Unbounded_String_Sets.Empty_Set;
         for Index in ALIs.First .. ALIs.Last loop
            --  ??? The ALI table seems to incldue some entries twice, but
            --  that is because some of them are null-terminated. See
            --  O714-006; this is the workaround for now.
            Nam := To_Unbounded_String
              (Name_String (Name_Id (Full_Lib_File_Name
                                       (ALIs.Table (Index).Afile))));
            Nam := Trim (Source => Nam,
                         Left   => Null_Set,
                         Right  => To_Set (Character'Val (0)));
            if not Read_Files.Contains (Nam) then
               Read_Files.Insert (Nam);
               Load_GG_Info_From_ALI (ALIs.Table (Index).Afile);
            end if;
         end loop;
      end;

      if Debug_GG_Read_Timing then
         Note_Time ("gg_read - ali files read");
      end if;

      if Debug_Print_Info_Sets_Read then
         --  Print all GG related info gathered from the ALI files.
         for Info of Subprogram_Info_List loop
            Write_Eol;
            Print_Subprogram_Phase_1_Info (Info);
         end loop;

         for C in State_Comp_Map.Iterate loop
            declare
               State : constant Entity_Name := Key (C);
               Constituents : constant Name_Sets.Set := Element (C);
            begin
               Write_Eol;
               Write_Line ("Abstract state " & To_String (State));

               Write_Line ("Constituents     :");
               for Name of Constituents loop
                  Write_Line ("   " & To_String (Name));
               end loop;
            end;
         end loop;

         --  Print all volatile info
         Write_Eol;

         Write_Line ("Async_Writers    :");
         for Name of Async_Writers_Vars loop
            Write_Line ("   " & To_String (Name));
         end loop;

         Write_Line ("Async_Readers    :");
         for Name of Async_Readers_Vars loop
            Write_Line ("   " & To_String (Name));
         end loop;

         Write_Line ("Effective_Reads  :");
         for Name of Effective_Reads_Vars loop
            Write_Line ("   " & To_String (Name));
         end loop;

         Write_Line ("Effective_Writes :");
         for Name of Effective_Writes_Vars loop
            Write_Line ("   " & To_String (Name));
         end loop;
      end if;

      --  Populate the All_Other_Subprograms set
      All_Other_Subprograms := All_Subprograms - GG_Subprograms;

      --  Initialize Local_Graph and Global_Graph
      Local_Graph  := Global_Graphs.Create;
      Global_Graph := Global_Graphs.Create;

      --  Create the Local_Graph
      Create_Local_Graph;
      if Debug_GG_Read_Timing then
         Note_Time ("gg_read - local graph done");
      end if;

      --  Create all vertices of the Global_Graph
      Create_All_Vertices;
      if Debug_GG_Read_Timing then
         Note_Time ("gg_read - vertices added");
      end if;

      --  Add all edges in the Global_Graph
      Add_All_Edges;
      if Debug_GG_Read_Timing then
         Note_Time ("gg_read - edges added");
      end if;

      --  Edit Proof_Ins
      Edit_Proof_Ins;
      if Debug_GG_Read_Timing then
         Note_Time ("gg_read - proof ins");
      end if;

      --  Now that the Globals Graph has been generated we set
      --  GG_Generated to True. Notice that we set GG_Generated to
      --  True before we remove edges leading to constants without
      --  variable input. The reasoning behind this is to use the
      --  generated globals instead of the computed globals when we
      --  call Get_Globals from within Has_Variable_Input.
      GG_Generated := True;

      --  Remove edges leading to constants which do not have variable
      --  input.
      Remove_Constants_Without_Variable_Input;
      if Debug_GG_Read_Timing then
         Note_Time ("gg_read - removed nonvariable constants");
      end if;

      if Debug_Print_Global_Graph then
         declare
            Common_Prefix : constant String :=
              Spec_File_Name_Without_Suffix
                (Enclosing_Comp_Unit_Node (GNAT_Root));

            LG_Filename   : constant String :=
              Common_Prefix & "_Locals_Graph";

            GG_Filename   : constant String :=
              Common_Prefix & "_Globals_Graph";
         begin
            Print_Global_Graph (Filename => LG_Filename,
                                G        => Local_Graph);

            Print_Global_Graph (Filename => GG_Filename,
                                G        => Global_Graph);
         end;
      end if;

      --  To speed up queries on constituents of state, we fill in a helper
      --  structure.
      Comp_State_Map := Name_Maps.Empty_Map;
      for C in State_Comp_Map.Iterate loop
         for Comp of Element (C) loop
            Comp_State_Map.Insert (Comp, Key (C));
         end loop;
      end loop;

      if Debug_GG_Read_Timing then
         Final_Time ("gg_read");
      end if;
   end GG_Read;

   --------------
   -- GG_Exist --
   --------------

   function GG_Exist (E : Entity_Id) return Boolean is
      Name : constant Entity_Name := To_Entity_Name (E);
   begin
      return GG_Exists_Cache.Contains (Name);
   end GG_Exist;

   -----------------------
   -- GG_Has_Refinement --
   -----------------------

   function GG_Has_Refinement (EN : Entity_Name) return Boolean is
   begin
      return State_Comp_Map.Contains (EN);
   end GG_Has_Refinement;

   -----------------------
   -- GG_Is_Constituent --
   -----------------------

   function GG_Is_Constituent (EN : Entity_Name) return Boolean is
   begin
      return Comp_State_Map.Contains (EN);
   end GG_Is_Constituent;

   -------------------------
   -- GG_Get_Constituents --
   -------------------------

   function GG_Get_Constituents (EN : Entity_Name) return Name_Sets.Set is
   begin
      return (if State_Comp_Map.Contains (EN)
              then State_Comp_Map.Element (EN)
              else Name_Sets.Empty_Set);
   end GG_Get_Constituents;

   ------------------------
   -- GG_Enclosing_State --
   ------------------------

   function GG_Enclosing_State (EN : Entity_Name) return Entity_Name is
   begin
      return (if Comp_State_Map.Contains (EN)
              then Comp_State_Map.Element (EN)
              else Null_Entity_Name);
   end GG_Enclosing_State;

   ---------------------
   -- GG_Fully_Refine --
   ---------------------

   function GG_Fully_Refine (EN : Entity_Name) return Name_Sets.Set is
      NS       : Name_Sets.Set;
      Tmp_Name : Entity_Name;
   begin
      NS := GG_Get_Constituents (EN);

      while (for some S of NS => GG_Has_Refinement (S)) loop
         Tmp_Name := Null_Entity_Name;
         for S of NS loop
            if GG_Has_Refinement (S) then
               Tmp_Name := S;
               exit;
            end if;
         end loop;

         if Tmp_Name /= Null_Entity_Name then
            NS.Union (GG_Get_Constituents (Tmp_Name));
            NS.Exclude (Tmp_Name);
         end if;
      end loop;

      return NS;
   end GG_Fully_Refine;

   --------------------
   -- GG_Get_Globals --
   --------------------

   procedure GG_Get_Globals (E           : Entity_Id;
                             S           : Flow_Scope;
                             Proof_Reads : out Flow_Id_Sets.Set;
                             Reads       : out Flow_Id_Sets.Set;
                             Writes      : out Flow_Id_Sets.Set)
   is
      MR_Proof_Reads  : Name_Sets.Set := Name_Sets.Empty_Set;
      MR_Reads        : Name_Sets.Set := Name_Sets.Empty_Set;
      MR_Writes       : Name_Sets.Set := Name_Sets.Empty_Set;
      --  The above 3 sets will contain the most refined views of
      --  their respective globals.

      Subprogram_Name : constant Entity_Name :=
        To_Entity_Name (E);
      --  Holds the Entity_Name of the subprogram

      G_Proof_Ins     : constant Global_Id :=
        Global_Id'(Kind => Proof_Ins_Kind,
                   Name => Subprogram_Name);
      G_Ins           : constant Global_Id :=
        Global_Id'(Kind => Ins_Kind,
                   Name => Subprogram_Name);
      G_Outs          : constant Global_Id :=
        Global_Id'(Kind => Outs_Kind,
                   Name => Subprogram_Name);
      --  The above 3 Global_Ids correspond to the subprogram's Ins,
      --  Outs and Proof_Ins.

      V_Proof_Ins     : constant Vertex_Id :=
        Global_Graph.Get_Vertex (G_Proof_Ins);
      V_Ins           : constant Vertex_Id :=
        Global_Graph.Get_Vertex (G_Ins);
      V_Outs          : constant Vertex_Id :=
        Global_Graph.Get_Vertex (G_Outs);
      --  The above 3 Vertex_Ids correspond to the subprogram's Ins,
      --  Outs and Proof_Ins.

      procedure Up_Project
        (Most_Refined      : Name_Sets.Set;
         Final_View        : out Name_Sets.Set;
         Processing_Writes : Boolean := False);
      --  Distinguishes between simple vars and constituents. For
      --  constituents, it checks if they are visible and if they are
      --  NOT we check if their enclosing state is. If the enclosing
      --  state is visible then return that (otherwise repeat the
      --  process). When Processing_Writes is set, we also check if
      --  all constituents are used and if they are not we need also
      --  add them on the Reads set.

      ----------------
      -- Up_Project --
      ----------------

      procedure Up_Project
        (Most_Refined      : Name_Sets.Set;
         Final_View        : out Name_Sets.Set;
         Processing_Writes : Boolean := False)
      is
         Abstract_States : Name_Sets.Set := Name_Sets.Empty_Set;
      begin
         --  Initializing Final_View to empty
         Final_View := Name_Sets.Empty_Set;

         for N of Most_Refined loop
            if GG_Enclosing_State (N) /= Null_Entity_Name and then
              (Find_Entity (N) = Empty or else
                 not Is_Visible (Find_Entity (N), S))
            then
               declare
                  Var               : Entity_Name :=
                    (if Find_Entity (N) /= Empty
                       and then Is_Visible (Find_Entity (N), S)
                     then N
                     else GG_Enclosing_State (N));
                  ES                : Entity_Name := GG_Enclosing_State (N);
                  Is_Abstract_State : Boolean     := False;
               begin
                  while Find_Entity (ES) = Empty or else
                    not Is_Visible (Find_Entity (ES), S)
                  loop
                     Is_Abstract_State := True;
                     Var := ES;

                     if GG_Enclosing_State (ES) /= Null_Entity_Name then
                        ES := GG_Enclosing_State (ES);
                     else
                        --  We cannot go any further up and we still
                        --  do not have visibility of the variable or
                        --  state abstraction that we are making use
                        --  of. This means that the user has neglected
                        --  to provide some state abstraction and the
                        --  refinement thereof. Unfortunately, we
                        --  might now refer to a variable or state
                        --  that the caller should not have vision of.
                        exit;
                     end if;
                  end loop;

                  Final_View.Include (Var);

                  --  We add the enclosing abstract state that we just
                  --  added to the Final_View set to the
                  --  Abstract_States set.
                  if Is_Abstract_State then
                     Abstract_States.Include (Var);
                  end if;
               end;
            else
               --  Add variables that are directly visible or do not
               --  belong to any state abstraction to the Final_View
               --  set.
               Final_View.Include (N);
            end if;
         end loop;

         --  If we Write some but not all constituents of a state
         --  abstraction then this state abstraction is also a Read.
         if Processing_Writes then
            for AS of Abstract_States loop
               declare
                  Constituents : constant Name_Sets.Set :=
                    GG_Fully_Refine (AS);
               begin
                  if not (for all C of Constituents =>
                            Most_Refined.Contains (C))
                  then
                     Reads.Include (Get_Flow_Id (AS, In_View, S));
                  end if;
               end;
            end loop;
         end if;
      end Up_Project;

   --  Start of processing for GG_Get_Globals

   begin
      --  Initialize the Proof_Reads, Reads and Writes sets
      Proof_Reads := Flow_Id_Sets.Empty_Set;
      Reads       := Flow_Id_Sets.Empty_Set;
      Writes      := Flow_Id_Sets.Empty_Set;

      --  Calculate MR_Proof_Reads, MR_Reads and MR_Writes
      declare
         function Calculate_MR (Start : Vertex_Id) return Name_Sets.Set;
         --  Returns a set of all vertices that can be reached from
         --  Start and are of the Variable_Kind.

         ------------------
         -- Calculate_MR --
         ------------------

         function Calculate_MR (Start : Vertex_Id) return Name_Sets.Set is
            NS : Name_Sets.Set := Name_Sets.Empty_Set;
            G  : Global_Id;
         begin
            for V of Global_Graph.Get_Collection (Start, Out_Neighbours) loop
               G := Global_Graph.Get_Key (V);

               if G.Kind = Variable_Kind then
                  NS.Include (G.Name);
               end if;
            end loop;

            return NS;
         end Calculate_MR;

      begin
         MR_Proof_Reads := Calculate_MR (V_Proof_Ins);
         MR_Reads       := Calculate_MR (V_Ins);
         MR_Writes      := Calculate_MR (V_Outs);
      end;

      --  Up project variables based on scope S and give Flow_Ids
      --  their correct views.
      declare
         Temp_NS : Name_Sets.Set;

         function To_Flow_Id_Set
           (NS   : Name_Sets.Set;
            View : Parameter_Variant)
            return Flow_Id_Sets.Set;
         --  Takes a Name_Set and returns a set of Flow_Id_Set

         --------------------
         -- To_Flow_Id_Set --
         --------------------

         function To_Flow_Id_Set
           (NS   : Name_Sets.Set;
            View : Parameter_Variant)
            return Flow_Id_Sets.Set
         is
            FS : Flow_Id_Sets.Set := Flow_Id_Sets.Empty_Set;
         begin
            for N of NS loop
               FS.Include (Get_Flow_Id (N, View, S));
            end loop;

            return FS;
         end To_Flow_Id_Set;

      begin
         Up_Project (Most_Refined => MR_Proof_Reads,
                     Final_View   => Temp_NS);
         Proof_Reads.Union (To_Flow_Id_Set (Temp_NS, In_View));

         Up_Project (Most_Refined => MR_Reads,
                     Final_View   => Temp_NS);
         Reads.Union (To_Flow_Id_Set (Temp_NS, In_View));

         Up_Project (Most_Refined      => MR_Writes,
                     Final_View        => Temp_NS,
                     Processing_Writes => True);
         Writes.Union (To_Flow_Id_Set (Temp_NS, Out_View));
      end;
   end GG_Get_Globals;

   -----------------------------------
   -- GG_Get_All_State_Abstractions --
   -----------------------------------

   function GG_Get_All_State_Abstractions return Name_Sets.Set is
      Tmp : Name_Sets.Set := Name_Sets.Empty_Set;
   begin
      for C in State_Comp_Map.Iterate loop
         Tmp.Insert (Key (C));
      end loop;

      return Tmp;
   end GG_Get_All_State_Abstractions;

   --------------------
   -- GG_Is_Volatile --
   --------------------

   function GG_Is_Volatile (EN : Entity_Name) return Boolean is
   begin
      return All_Volatile_Vars.Contains (EN);
   end GG_Is_Volatile;

   --------------------------
   -- GG_Has_Async_Writers --
   --------------------------

   function GG_Has_Async_Writers (EN : Entity_Name) return Boolean is
   begin
      return Async_Writers_Vars.Contains (EN);
   end GG_Has_Async_Writers;

   --------------------------
   -- GG_Has_Async_Readers --
   --------------------------

   function GG_Has_Async_Readers (EN : Entity_Name) return Boolean is
   begin
      return Async_Readers_Vars.Contains (EN);
   end GG_Has_Async_Readers;

   ----------------------------
   -- GG_Has_Effective_Reads --
   ----------------------------

   function GG_Has_Effective_Reads (EN : Entity_Name) return Boolean is
   begin
      return Effective_Reads_Vars.Contains (EN);
   end GG_Has_Effective_Reads;

   -----------------------------
   -- GG_Has_Effective_Writes --
   -----------------------------

   function GG_Has_Effective_Writes (EN : Entity_Name) return Boolean is
   begin
      return Effective_Writes_Vars.Contains (EN);
   end GG_Has_Effective_Writes;

   -----------------------------
   -- Is_Potentially_Blocking --
   -----------------------------

   function Is_Potentially_Blocking (E : Entity_Id) return Boolean
   is
      EN : constant Entity_Name := To_Entity_Name (E);
      --  Entity name

      Protected_Object_E : constant Entity_Id := Scope (E);
      --  Entity of the enclosing protected object

      Ins_GID       : constant Global_Id := (Kind => Ins_Kind,
                                             Name => EN);

      Outs_GID      : constant Global_Id := (Kind => Outs_Kind,
                                             Name => EN);

      Proof_Ins_GID : constant Global_Id := (Kind => Proof_Ins_Kind,
                                             Name => EN);
      --  Global_Ids that collectively represent subprogram EN

      function Calls_Potentially_Blocking_Subprogram
        (GID : Global_Id) return Boolean with
        Pre => GID.Kind in Ins_Kind | Proof_Ins_Kind | Outs_Kind;
      --  Check for calls to potentially blocking subprograms of a given Kind

      function Calls_Same_Target_Object (S : Global_Id) return Boolean;
      --  Check if subprogram S calls the enclosing protected object of EN

      -------------------------------------------
      -- Calls_Potentially_Blocking_Subprogram --
      -------------------------------------------

      function Calls_Potentially_Blocking_Subprogram
        (GID : Global_Id) return Boolean
      is
         Subp_V : constant Vertex_Id := Global_Graph.Get_Vertex (GID);
         --  Vertex that represents called subprogram

         Callee : Global_Id;
      begin
         for V of Global_Graph.Get_Collection (Subp_V, Out_Neighbours) loop

            Callee := Global_Graph.Get_Key (V);

            if Callee.Kind in Proof_Ins_Kind | Ins_Kind | Outs_Kind then
               --  Check for potentially blocking constructs
               if not Nonblocking_Subprograms_Set.Contains (Callee.Name) then
                  return True;
               end if;

               --  Check for external calls on a protected subprogram with the
               --  same target object as that of the protected action???
               declare
                  Callee_E : constant Entity_Id := Find_Entity (Callee.Name);
               begin
                  --  Entities from other compilation units have empty id???
                  if Callee_E = Empty
                    or else not Scope_Within_Or_Same (Scope (Callee_E),
                                                      Protected_Object_E)
                  then
                     if Calls_Same_Target_Object (Callee) then
                        return True;
                     end if;
                  end if;
               end;
            end if;

         end loop;

         return False;

      end Calls_Potentially_Blocking_Subprogram;

      ------------------------------
      -- Calls_Same_Target_Object --
      ------------------------------

      function Calls_Same_Target_Object (S : Global_Id) return Boolean is
         Subp_V : constant Vertex_Id := Global_Graph.Get_Vertex (S);
         --  Vertex that represents subprogram S

         Callee : Global_Id;
         --  Vertex that represent subprogram called by S
      begin
         --  Iterate over variables accessed by subprogram S
         for V of Global_Graph.Get_Collection (Subp_V, Out_Neighbours) loop

            Callee := Global_Graph.Get_Key (V);

            if Callee.Kind in Ins_Kind | Outs_Kind | Proof_Ins_Kind then
               declare
                  Callee_E : constant Entity_Id := Find_Entity (Callee.Name);
               begin
                  if Callee_E /= Empty and then
                    Scope (Callee_E) = Protected_Object_E
                  then
                     return True;
                  end if;
               end;

            end if;

         end loop;

         return False;
      end Calls_Same_Target_Object;

   --  Start of processing for Is_Potentially_Blocking

   begin
      return (not Nonblocking_Subprograms_Set.Contains (EN))
        or else Calls_Potentially_Blocking_Subprogram (Ins_GID)
        or else Calls_Potentially_Blocking_Subprogram (Outs_GID)
        or else Calls_Potentially_Blocking_Subprogram (Proof_Ins_GID);
   end Is_Potentially_Blocking;

end Flow_Generated_Globals;
