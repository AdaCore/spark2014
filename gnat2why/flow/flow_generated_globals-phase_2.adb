------------------------------------------------------------------------------
--                                                                          --
--                           GNAT2WHY COMPONENTS                            --
--                                                                          --
--       F L O W . G E N E R A T E D _ G L O B A L S . P H A S E _ 2        --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--               Copyright (C) 2014-2016, Altran UK Limited                 --
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

with GNAT.Regpat;                use GNAT.Regpat;
with Serialisation;              use Serialisation;
with Ada.Containers.Hashed_Sets;
with Ada.Strings.Maps;           use Ada.Strings.Maps;
with Ada.Strings.Unbounded;      use Ada.Strings.Unbounded;
with Ada.Text_IO;                use Ada.Text_IO;
with Ada.Text_IO.Unbounded_IO;   use Ada.Text_IO.Unbounded_IO;

with ALI;                        use ALI;
with Namet;                      use Namet;
with Osint;                      use Osint;
with Output;                     use Output;
with Sem_Util;                   use Sem_Util;
with Snames;                     use Snames;

with Call;                       use Call;
with Gnat2Why_Args;
with Hashing;                    use Hashing;
with SPARK2014VSN;               use SPARK2014VSN;
with SPARK_Definition;           use SPARK_Definition;
with SPARK_Frame_Conditions;     use SPARK_Frame_Conditions;
with SPARK_Util;                 use SPARK_Util;

with Flow_Debug;                 use Flow_Debug;
with Flow_Utility;               use Flow_Utility;
with Graphs;

with Flow_Generated_Globals.ALI_Serialization;
use Flow_Generated_Globals.ALI_Serialization;

package body Flow_Generated_Globals.Phase_2 is

   ---------------------------------------------------
   -- Regular expression for predefined subprograms --
   ---------------------------------------------------

   --  Any user-defined subprogram for which we do not know its blocking status
   --  (e.g. when its body is missing or is not in SPARK) is assumed to be
   --  potentially blocking. For predefined subprograms we never read their
   --  blocking status from ALI file, but assume that they are nonblocking.
   --  This assumption is valid, because user-defined subprograms that call a
   --  predefined potentially blocking subprogram have been already marked as
   --  potentially blocking.
   --
   --  However, here we still need to distinguish between user-defined and
   --  predefined subprograms and can only do this by their Entity_Name (i.e.
   --  string). We do this with regular expressions, which are more efficient
   --  than naive string matching. The regexp is a global constant and so it
   --  is compiled only once.

   Predefined : constant Pattern_Matcher :=
     Compile ("^(ada|interfaces|system)__");
   --  Regexp for predefined entities

   ----------------------------------------------------------------------
   --  Global_Id
   ----------------------------------------------------------------------

   type Global_Id_Kind is (Null_Global_Id,
                           --  Does not represent anything yet

                           Subprogram,
                           --  This kind should only be used in Local_Graphs

                           Inputs,
                           --  Represents subprogram's Inputs

                           Outputs,
                           --  Represents subprogram's Outputs

                           Proof_Ins,
                           --  Represents subprogram's Proof_Ins

                           Variable
                           --  Represents a global variable
                          );
   pragma Ordered (Global_Id_Kind);

   type Global_Id (Kind : Global_Id_Kind := Null_Global_Id) is record
      case Kind is
         when Null_Global_Id =>
            null;

         when others =>
            Name : Entity_Name;
      end case;
   end record;

   Empty_Global_Id : constant Global_Id := Global_Id'(Kind => Null_Global_Id);

   function Global_Hash (X : Global_Id) return Ada.Containers.Hash_Type
   is (if X.Kind = Null_Global_Id
       then Generic_Integer_Hash (-1)
       else Name_Hash (X.Name));

   -------------------
   -- Global_Graphs --
   -------------------

   type No_Colours is (Dummy_Color);
   --  Dummy type inhabited by only a single value (similar to unit type in
   --  OCaml); used to instantiate graphs with colorless edges.

   package Global_Graphs is new Graphs
     (Vertex_Key   => Global_Id,
      Key_Hash     => Global_Hash,
      Edge_Colours => No_Colours,
      Null_Key     => Empty_Global_Id,
      Test_Key     => "=");

   package Vertex_Sets is new Ada.Containers.Hashed_Sets
     (Element_Type        => Global_Graphs.Vertex_Id,
      Hash                => Global_Graphs.Vertex_Hash,
      Equivalent_Elements => Global_Graphs."=",
      "="                 => Global_Graphs."=");

   Global_Graph : Global_Graphs.Graph;
   --  A graph that represents the globals that each subprogram has as inputs,
   --  outputs and proof inputs.

   --------------------
   -- Tasking graphs --
   --------------------

   type Phase is (GG_Phase_1, GG_Phase_2);

   Tasking_Info_Bag :
     array (Phase, Tasking_Info_Kind) of Name_Graphs.Map :=
     (others => (others => Name_Graphs.Empty_Map));
   --  Maps from subprogram names to accessed objects
   --
   --  In phase 1 it is populated with objects directly accessed by each
   --  subprogram and stored in the ALI file. In phase 2 it is populated
   --  with objects directly and indirectly accessed by each subprogram.

   package Entity_Name_Graphs is new Graphs
     (Vertex_Key   => Entity_Name,
      Edge_Colours => No_Colours,
      Null_Key     => Entity_Name'Last,
      Key_Hash     => Name_Hash,
      Test_Key     => "=");
   --  Note: Null_Key is required by the Graphs API, but not used here; the
   --  'Last value is a dummy one.

   Protected_Operation_Call_Graph : Entity_Name_Graphs.Graph :=
     Entity_Name_Graphs.Create;
   --  Call graph rooted at protected operations for detecting potentially
   --  blocking statements.

   --  Vertices correspond to subprograms and edges correspond to subprogram
   --  calls.
   --
   --  Subprogram calls are provided by the front end, i.e. they are not
   --  affected by user's annotations. Unlike Global_Graph, it contains
   --  no objects.

   Tasking_Call_Graph : Entity_Name_Graphs.Graph := Entity_Name_Graphs.Create;
   --  Call graph for detecting ownership conflicts between tasks
   --
   --  Vertices correspond to subprograms, entries and tasks with specification
   --  in SPARK and a flow contract, either provided by the user or inferred
   --  from the body (otherwise they have no body or the body is not in SPARK).
   --  Edges correspond to subprogram calls.

   Ceiling_Priority_Call_Graph : Entity_Name_Graphs.Graph :=
     Entity_Name_Graphs.Create;
   --  Call graph for ceiling priority checks
   --
   --  It is similar to other call graphs, but rooted at task types, main-like
   --  subprograms and protected operations (i.e. entries, protected functions
   --  and protected procedures) in current compilation unit and is cut at
   --  protected operations.

   use type Entity_Name_Graphs.Vertex_Id;

   Nonblocking_Subprograms : Name_Sets.Set := Name_Sets.Empty_Set;
   --  Subprograms, entries and tasks that do not contain potentially blocking
   --  statements (but still may call another blocking subprogram).

   package Entity_Name_To_Priorities_Maps is
     new Ada.Containers.Hashed_Maps
       (Key_Type        => Entity_Name,
        Element_Type    => Object_Priority_Lists.List,
        Hash            => Name_Hash,
        Equivalent_Keys => "=",
        "="             => Object_Priority_Lists."=");
   --  Maps from variables containing protected objects to their static
   --  priorities; for priority ceiling checks.

   Protected_Objects : Entity_Name_To_Priorities_Maps.Map;

   use type Flow_Id_Sets.Set;
   use type Name_Sets.Set;

   use Name_Graphs;

   ----------------------------------------------------------------------
   --  Debug flags
   ----------------------------------------------------------------------

   Debug_Print_Info_Sets_Read        : constant Boolean := False;
   --  Enables printing of Subprogram_Info_Sets as read from ALI files

   Debug_Print_Global_Graph          : constant Boolean := True;
   --  Enables printing of the Global_Graph

   Debug_GG_Read_Timing              : constant Boolean := False;
   --  Enables timing information for gg_read

   Debug_Print_Generated_Initializes : constant Boolean := False;
   --  Enables printing of the generated initializes aspects

   ----------------------------------------------------------------------
   --  State information
   ----------------------------------------------------------------------

   State_Comp_Map : Name_Graphs.Map := Name_Graphs.Empty_Map;
   --  Mapping from abstract states to their constituents, i.e.
   --  abstract_state -> {constituents}

   Comp_State_Map : Name_Maps.Map   := Name_Maps.Empty_Map;
   --  A reverse of the above mapping, i.e. constituent -> abstract_state,
   --  which speeds up some queries. It is populated at the end of GG_Read from
   --  State_Comp_Map.

   State_Abstractions : Name_Sets.Set := Name_Sets.Empty_Set;
   --  State abstractions that the GG knows of

   ----------------------------------------------------------------------
   --  Local state
   ----------------------------------------------------------------------

   GG_Exists_Cache : Name_Sets.Set := Name_Sets.Empty_Set;
   --  This should be equivalent to:
   --     {x.name for all x of Subprogram_Info_List}

   ----------------------------------------------------------------------
   --  Initializes information
   ----------------------------------------------------------------------

   type Initializes_Info is record
      LHS       : Name_Sets.Set := Name_Sets.Empty_Set;
      LHS_Proof : Name_Sets.Set := Name_Sets.Empty_Set;
      RHS       : Name_Sets.Set := Name_Sets.Empty_Set;
      RHS_Proof : Name_Sets.Set := Name_Sets.Empty_Set;
   end record;

   package Initializes_Aspects_Maps is new Ada.Containers.Hashed_Maps
     (Key_Type        => Entity_Name,
      Element_Type    => Initializes_Info,
      Hash            => Name_Hash,
      Equivalent_Keys => "=");

   Initializes_Aspects_Map : Initializes_Aspects_Maps.Map :=
     Initializes_Aspects_Maps.Empty_Map;

   All_Initialized_Names   : Name_Sets.Set := Name_Sets.Empty_Set;
   --  This set of names will hold all variables and state abstractions
   --  that we know are initialized.

   Package_To_Locals_Map   : Name_Graphs.Map := Name_Graphs.Empty_Map;
   --  package -> {local variables}
   --
   --  This maps packages to their local variables

   ----------------------------------------------------------------------
   --  Volatile information
   ----------------------------------------------------------------------

   All_Volatile_Vars     : Name_Sets.Set := Name_Sets.Empty_Set;
   Async_Writers_Vars    : Name_Sets.Set := Name_Sets.Empty_Set;
   Async_Readers_Vars    : Name_Sets.Set := Name_Sets.Empty_Set;
   Effective_Reads_Vars  : Name_Sets.Set := Name_Sets.Empty_Set;
   Effective_Writes_Vars : Name_Sets.Set := Name_Sets.Empty_Set;
   --  Volatile information

   ----------------------------------------------------------------------
   --  Local subprograms
   ----------------------------------------------------------------------

   function Fully_Refine (EN : Entity_Name) return Name_Sets.Set;
   --  Returns the most refined constituents of variable or state abstraction

   function GG_Enclosing_State (EN : Entity_Name) return Any_Entity_Name;
   --  Returns the Entity_Name of the directly enclosing state. If one
   --  does not exist it returns Null_Entity_Name.

   procedure GG_Get_MR_Globals (EN          : Entity_Name;
                                Proof_Reads : out Name_Sets.Set;
                                Reads       : out Name_Sets.Set;
                                Writes      : out Name_Sets.Set);
   --  Gets the most refined proof reads, reads and writes globals of EN

   procedure Register_Task_Object
     (Type_Name : Entity_Name;
      Object    : Task_Object);
   --  Register an instance Object whose type is a task type Type_Name; this
   --  will be either an explicit instance or the implicit environment task
   --  for the "main" subprogram.

   procedure Up_Project
     (Most_Refined      : Name_Sets.Set;
      Final_View        : out Name_Sets.Set;
      Scope             : Flow_Scope;
      Reads             : in out Flow_Id_Sets.Set;
      Processing_Writes : Boolean := False)
   with Pre  => (if not Processing_Writes then Reads.Is_Empty),
        Post => (if not Processing_Writes then Reads.Is_Empty);
   --  Distinguishes between simple vars and constituents. For constituents, it
   --  checks if they are visible and if they are NOT we check if their
   --  enclosing state is. If the enclosing state is visible then return that
   --  (otherwise repeat the process). When Processing_Writes is set, we also
   --  check if all constituents are used and if they are not we also add them
   --  on the Reads set.

   ----------------------------------------------------------------------
   --  Debug routines
   ----------------------------------------------------------------------

   procedure Print_Tasking_Info_Bag (P : Phase);
   --  Display the tasking-related information

   procedure Print_Global_Phase_1_Info (Info : Global_Phase_1_Info);
   --  Prints all global related info of an entity

   procedure Print_Global_Graph (Filename : String;
                                 G        : Global_Graphs.Graph);
   --  Writes dot and pdf files for the Global_Graph

   procedure Print_Generated_Initializes_Aspects;
   --  Prints all the generated initializes aspects

   procedure Print_Name_Set (Header : String; Set : Name_Sets.Set);
   --  Print Header followed by elements of Set

   ---------------------
   -- Fully_Refine --
   ---------------------

   function Fully_Refine (EN : Entity_Name) return Name_Sets.Set is
      Refined : Name_Sets.Set := Name_Sets.Empty_Set;

      procedure Expand (State : Entity_Name);
      --  Recursively expand state into its constituents

      ------------
      -- Expand --
      ------------

      procedure Expand (State : Entity_Name) is
         Constituents : constant Name_Graphs.Cursor :=
           State_Comp_Map.Find (State);
      begin
         if Name_Graphs.Has_Element (Constituents) then
            for Constituent of State_Comp_Map (Constituents) loop
               Expand (Constituent);
            end loop;
         else
            Refined.Insert (State);
         end if;
      end Expand;

   begin
      Expand (EN);

      return Refined;
   end Fully_Refine;

   -----------------------------------
   -- GG_Get_All_State_Abstractions --
   -----------------------------------

   function GG_Get_State_Abstractions return Name_Sets.Set is
   begin
      return State_Abstractions;
   end GG_Get_State_Abstractions;

   --------------------
   -- GG_Get_Globals --
   --------------------

   procedure GG_Get_Globals (E           : Entity_Id;
                             S           : Flow_Scope;
                             Proof_Reads : out Flow_Id_Sets.Set;
                             Reads       : out Flow_Id_Sets.Set;
                             Writes      : out Flow_Id_Sets.Set)
   is
      MR_Proof_Reads : Name_Sets.Set := Name_Sets.Empty_Set;
      MR_Reads       : Name_Sets.Set := Name_Sets.Empty_Set;
      MR_Writes      : Name_Sets.Set := Name_Sets.Empty_Set;
      --  The above 3 sets will contain the most refined views of their
      --  respective globals.

      Temp_NS : Name_Sets.Set;
      Unused  : Flow_Id_Sets.Set;

   begin
      --  Initialize the Proof_Reads, Reads and Writes sets
      Proof_Reads := Flow_Id_Sets.Empty_Set;
      Reads       := Flow_Id_Sets.Empty_Set;
      Writes      := Flow_Id_Sets.Empty_Set;

      --  Call GG_Get_MR_Globals to calculate MR_Proof_Reads, MR_Reads and
      --  MR_Writes.
      GG_Get_MR_Globals (To_Entity_Name (E),
                         MR_Proof_Reads,
                         MR_Reads,
                         MR_Writes);

      --  Up project variables based on scope S and give Flow_Ids
      --  their correct views.
      Up_Project (Most_Refined => MR_Proof_Reads,
                  Final_View   => Temp_NS,
                  Scope        => S,
                  Reads        => Unused);
      Proof_Reads.Union (To_Flow_Id_Set (Temp_NS, In_View, S));

      Up_Project (Most_Refined => MR_Reads,
                  Final_View   => Temp_NS,
                  Scope        => S,
                  Reads        => Unused);
      Reads.Union (To_Flow_Id_Set (Temp_NS, In_View, S));

      Up_Project (Most_Refined      => MR_Writes,
                  Final_View        => Temp_NS,
                  Scope             => S,
                  Reads             => Reads,
                  Processing_Writes => True);
      Writes.Union (To_Flow_Id_Set (Temp_NS, Out_View, S));
   end GG_Get_Globals;

   ------------------------
   -- GG_Get_Initializes --
   ------------------------

   function GG_Get_Initializes
     (EN : Entity_Name;
      S  : Flow_Scope)
      return Dependency_Maps.Map
   is
   begin
      if GG_Exists_Cache.Contains (EN) then
         --  Retrieve the relevant Name_Dependency_Map, up project it to S and
         --  then convert it into a Dependency_Map.
         declare
            Pkg       : constant Entity_Id := Find_Entity (EN);
            LHS_Scope : constant Flow_Scope :=
              (if Present (Pkg)
               then Flow_Scope'(Ent     => Pkg,
                                Section => Spec_Part)
               else S);

            DM : Dependency_Maps.Map;
            II : Initializes_Info renames Initializes_Aspects_Map (EN);

            All_LHS_UP   : Name_Sets.Set;
            LHS_UP       : Name_Sets.Set;
            LHS_Proof_UP : Name_Sets.Set;
            RHS_UP       : Name_Sets.Set;
            RHS_Proof_UP : Name_Sets.Set;

            To_Remove    : Flow_Id_Sets.Set := Flow_Id_Sets.Empty_Set;
            --  This set will hold the names of non fully initialized states.
            --  These will have to be removed from the left hand side sets.

            FS_LHS       : Flow_Id_Sets.Set;
            FS_LHS_Proof : Flow_Id_Sets.Set;
            FS_RHS       : Flow_Id_Sets.Set;
            FS_RHS_Proof : Flow_Id_Sets.Set;
            --  These will hold the final flow sets that will be used to
            --  populate the dependency map.

            Unused : Flow_Id_Sets.Set;

         begin
            --  Up project left hand side
            Up_Project (Most_Refined      => II.LHS or II.LHS_Proof,
                        Final_View        => All_LHS_UP,
                        Scope             => LHS_Scope,
                        Reads             => To_Remove,
                        Processing_Writes => True);

            Up_Project (Most_Refined => II.LHS,
                        Final_View   => LHS_UP,
                        Scope        => LHS_Scope,
                        Reads        => Unused);

            Up_Project (Most_Refined => II.LHS_Proof,
                        Final_View   => LHS_Proof_UP,
                        Scope        => LHS_Scope,
                        Reads        => Unused);

            --  Up project right hand side
            Up_Project (Most_Refined => II.RHS,
                        Final_View   => RHS_UP,
                        Scope        => S,
                        Reads        => Unused);

            Up_Project (Most_Refined => II.RHS_Proof,
                        Final_View   => RHS_Proof_UP,
                        Scope        => S,
                        Reads        => Unused);

            --  Populate and return DM
            FS_LHS       := To_Flow_Id_Set (LHS_UP);
            FS_LHS_Proof := To_Flow_Id_Set (LHS_Proof_UP);
            FS_RHS       := To_Flow_Id_Set (RHS_UP);
            FS_RHS_Proof := To_Flow_Id_Set (RHS_Proof_UP);

            --  Remove state abstractions that are only partially initialized
            --  from the left hand side.
            FS_LHS.Difference (To_Remove);
            FS_LHS_Proof.Difference (To_Remove);

            --  Add regular variables
            for F of FS_LHS loop
               DM.Insert (F, FS_RHS);
            end loop;
            --  Add proof variables
            for F of FS_LHS_Proof loop
               DM.Insert (F, FS_RHS_Proof);
            end loop;

            return DM;
         end;

      --  If we have no info for this package then we also did not generate the
      --  initializes aspect for it.

      else
         return Dependency_Maps.Empty_Map;
      end if;
   end GG_Get_Initializes;

   ----------------------------
   -- GG_Get_Local_Variables --
   ----------------------------

   function GG_Get_Local_Variables (EN : Entity_Name) return Name_Sets.Set is
     (if GG_Exists_Cache.Contains (EN)
      then Package_To_Locals_Map (EN)
      else Name_Sets.Empty_Set);

   -----------------------
   -- GG_Get_MR_Globals --
   -----------------------

   procedure GG_Get_MR_Globals (EN          : Entity_Name;
                                Proof_Reads : out Name_Sets.Set;
                                Reads       : out Name_Sets.Set;
                                Writes      : out Name_Sets.Set)
   is
      use Global_Graphs;

      G_Proof_Ins : constant Global_Id :=
        Global_Id'(Kind => Proof_Ins,
                   Name => EN);
      G_Ins       : constant Global_Id :=
        Global_Id'(Kind => Inputs,
                   Name => EN);
      G_Outs      : constant Global_Id :=
        Global_Id'(Kind => Outputs,
                   Name => EN);
      --  The above 3 Global_Ids correspond to the subprogram's Ins,
      --  Outs and Proof_Ins.

      V_Proof_Ins : constant Vertex_Id :=
        Global_Graph.Get_Vertex (G_Proof_Ins);
      V_Ins       : constant Vertex_Id :=
        Global_Graph.Get_Vertex (G_Ins);
      V_Outs      : constant Vertex_Id :=
        Global_Graph.Get_Vertex (G_Outs);
      --  The above 3 Vertex_Ids correspond to the subprogram's Ins,
      --  Outs and Proof_Ins.

      function Calculate_MR (Start : Vertex_Id) return Name_Sets.Set;
      --  Returns a set of all vertices that can be reached from Start and are
      --  of the Variable.

      ------------------
      -- Calculate_MR --
      ------------------

      function Calculate_MR (Start : Vertex_Id) return Name_Sets.Set is
         NS : Name_Sets.Set := Name_Sets.Empty_Set;

      begin
         for V of Global_Graph.Get_Collection (Start, Out_Neighbours) loop
            declare
               G : constant Global_Id := Global_Graph.Get_Key (V);
            begin
               if G.Kind = Variable then
                  NS.Union (Fully_Refine (G.Name));
               end if;
            end;
         end loop;

         return NS;
      end Calculate_MR;

      --  Start of processing for GG_Get_MR_Globals

   begin
      --  Calculate MR_Proof_Reads, MR_Reads and MR_Writes
      Proof_Reads := Calculate_MR (V_Proof_Ins);
      Reads       := Calculate_MR (V_Ins);
      Writes      := Calculate_MR (V_Outs);
   end GG_Get_MR_Globals;

   ----------------
   -- Up_Project --
   ----------------

   procedure Up_Project
     (Most_Refined      : Name_Sets.Set;
      Final_View        : out Name_Sets.Set;
      Scope             : Flow_Scope;
      Reads             : in out Flow_Id_Sets.Set;
      Processing_Writes : Boolean := False)
   is
      Abstract_States : Name_Sets.Set := Name_Sets.Empty_Set;

   begin
      --  Initialize Final_View
      Final_View := Name_Sets.Empty_Set;

      for N of Most_Refined loop

         --  We climb the hierarchy of abstract states until we find a visible
         --  one (because of scope visibility rules) or a one without enclosing
         --  abstract state (because it must be visible anyway).

         declare
            Var_Name   : Entity_Name := N;
            Var_Entity : Entity_Id;

            Enclosing_State : Any_Entity_Name;

            function Is_Abstract_State return Boolean is
              (Var_Name /= N);
            --  If the visible name is different from the original one, then
            --  the original one must have been hidden in an abstract state.

         begin
            loop
               Var_Entity      := Find_Entity (Var_Name);
               Enclosing_State := GG_Enclosing_State (Var_Name);

               if Enclosing_State = Null_Entity_Name
                 or else (Present (Var_Entity)
                          and then Is_Visible (Var_Entity, Scope))
               then
                  exit;
               end if;

               Var_Name := Enclosing_State;
            end loop;

            Final_View.Include (Var_Name);

            if Processing_Writes and then Is_Abstract_State
            then
               Abstract_States.Include (Var_Name);
            end if;
         end;
      end loop;

      --  If we Write some but not all constituents of a state abstraction then
      --  this state abstraction is also a Read.
      for AS of Abstract_States loop
         declare
            Constituents : constant Name_Sets.Set := Fully_Refine (AS);

         begin
            if not (for all C of Constituents => Most_Refined.Contains (C))
            then
               Reads.Include (Get_Flow_Id (AS, In_View, Scope));
            end if;
         end;
      end loop;
   end Up_Project;

   -------------
   -- GG_Read --
   -------------

   procedure GG_Read (GNAT_Root : Node_Id) is
      All_Globals           : Name_Sets.Set;
      --  Contains all global variables

      GG_Subprograms        : Name_Sets.Set;
      --  Contains all subprograms for which a GG entry exists

      All_Subprograms       : Name_Sets.Set;
      --  Contains all subprograms that we know of, even if a GG entry does not
      --  exist for them.

      All_Other_Subprograms : Name_Sets.Set;
      --  Contains all subprograms for which a GG entry does not exist
      --  ??? rename to No_GG_Subprograms?

      Local_Graph : Global_Graphs.Graph;
      --  A graph that represents the hierarchy of subprograms (which
      --  subprogram is nested in which one); used to determine which
      --  local variables may act as globals to which subprograms.

      Subprogram_Info_List : Global_Info_Lists.List;
      --  Information about subprograms from the "generated globals" algorithm

      Package_Info_List : Global_Info_Lists.List;
      --  Information about packages from the "generated globals" algorithm

      procedure Add_All_Edges;
      --  Reads the populated Subprogram_Info_List and generates all the edges
      --  of the Global_Graph. While adding edges we consult the Local_Graph so
      --  as not to add edges to local variables.
      --  Also, creates edges for (conditional and unconditional) subprogram
      --  calls in the tasking-related call graphs.

      procedure Create_All_Vertices;
      --  Creates all the vertices of the Global_Graph and subprogram vertices
      --  in the Tasking_Graph.

      procedure Create_Local_Graph;
      --  Creates the Local_Graph. This graph will be used to prevent adding
      --  edges to local variables on the Global_Graph.

      procedure Edit_Proof_Ins;
      --  A variable cannot be simultaneously a Proof_In and an Input of
      --  a subprogram. In this case we need to remove the Proof_In edge.
      --  Furthermore, a variable cannot be simultaneously a Proof_In and
      --  an Output (but not an input). In this case we need to change the
      --  Proof_In variable into an Input.

      procedure Generate_Initializes_Aspects;
      --  Once the global graph has been generated, we use it to generate the
      --  Initializes aspects. We also take this opportunity to populate the
      --  Package_To_Locals_Map.

      procedure Load_GG_Info_From_ALI (ALI_File_Name : File_Name_Type);
      --  Loads the GG info from an ALI file and stores them in the
      --  Subprogram_Info_List, State_Comp_Map and volatile info sets.

      procedure Note_Time (Message : String);
      --  Record timing statistics (but only in timing debug mode)

      procedure Remove_Constants_Without_Variable_Input;
      --  Removes edges leading to constants without variable input

      procedure Process_Tasking_Graph;
      --  Do transitive closure of the tasking graph and put the resulting
      --  information back to bag with tasking-related information.

      -------------------
      -- Add_All_Edges --
      -------------------

      procedure Add_All_Edges is
         use Global_Graphs;

         function Edge_Selector (A, B : Vertex_Id) return Boolean;
         --  Check if we should add the given edge to the graph based weather
         --  it is in the local graph or not.

         -------------------
         -- Edge_Selector --
         -------------------

         function Edge_Selector (A, B : Vertex_Id) return Boolean is
            Key_A :          Global_Id := Global_Graph.Get_Key (A);
            Key_B : constant Global_Id := Global_Graph.Get_Key (B);
         begin
            if Key_B.Kind /= Variable
              or else Key_A.Kind not in Proof_Ins | Inputs | Outputs
            then
               --  We only need to consult the Local_Graph when attempting
               --  to establish a link between a subprogram and a variable.
               return True;
            end if;

            --  Convert kind so that it can be used on Local_Graph
            Key_A := Global_Id'(Kind => Subprogram,
                                Name => Key_A.Name);

            declare
               Vertex_A, Vertex_B : Vertex_Id;
            begin
               Vertex_A := Local_Graph.Get_Vertex (Key_A);

               if Vertex_A = Null_Vertex then
                  return True;
               end if;

               Vertex_B := Local_Graph.Get_Vertex (Key_B);

               if Vertex_B = Null_Vertex then
                  return True;
               end if;

               --  Check if local variable B can act as global of subprogram A
               return Local_Graph.Edge_Exists (Vertex_B, Vertex_A);
            end;
         end Edge_Selector;

      --  Start of processing for Add_All_Edges

      begin
         --  Go through the Subprogram_Info_List and add edges
         for Info of Subprogram_Info_List loop
            declare
               G_Ins : constant Global_Id (Inputs) :=
                 (Kind => Inputs,
                  Name => Info.Name);

               G_Outs : constant Global_Id (Outputs) :=
                 (Kind => Outputs,
                  Name => Info.Name);

               G_Proof_Ins : constant Global_Id (Proof_Ins) :=
                 (Kind => Proof_Ins,
                  Name => Info.Name);

            begin
               --  Connect the subprogram's Proof_In variables to the
               --  subprogram's Proof_Ins vertex.
               for Input_Proof of Info.Inputs_Proof loop
                  Global_Graph.Add_Edge (G_Proof_Ins,
                                         Global_Id'(Kind => Variable,
                                                    Name => Input_Proof));
               end loop;

               --  Connect the subprogram's Input variables to the subprogram's
               --  Ins vertex.
               for Input of Info.Inputs loop
                  Global_Graph.Add_Edge (G_Ins,
                                         Global_Id'(Kind => Variable,
                                                    Name => Input));
               end loop;

               --  Connect the subprogram's Output variables to the
               --  subprogram's Outputs vertex.
               for Output of Info.Outputs loop
                  Global_Graph.Add_Edge (G_Outs,
                                         Global_Id'(Kind => Variable,
                                                    Name => Output));
               end loop;

               --  Connect the subprogram's Proof_Ins vertex to the callee's
               --  Ins and Proof_Ins vertices.
               for Proof_Call of Info.Proof_Calls loop
                  Global_Graph.Add_Edge (G_Proof_Ins,
                                         Global_Id'(Kind => Proof_Ins,
                                                    Name => Proof_Call));

                  Global_Graph.Add_Edge (G_Proof_Ins,
                                         Global_Id'(Kind => Inputs,
                                                    Name => Proof_Call));
               end loop;

               --  Connect the subprogram's Proof_Ins, Ins and Outs vertices
               --  respectively to the callee's Proof_Ins, Ins and Outs
               --  vertices.
               for Definite_Call of Info.Definite_Calls loop
                  Global_Graph.Add_Edge (G_Proof_Ins,
                                         Global_Id'(Kind => Proof_Ins,
                                                    Name => Definite_Call));

                  Global_Graph.Add_Edge (G_Ins,
                                         Global_Id'(Kind => Inputs,
                                                    Name => Definite_Call));

                  Global_Graph.Add_Edge (G_Outs,
                                         Global_Id'(Kind => Outputs,
                                                    Name => Definite_Call));
               end loop;

               --  As above but also add an edge from the subprogram's Ins
               --  vertex to the callee's Outs vertex.
               for Conditional_Call of Info.Conditional_Calls loop
                  Global_Graph.Add_Edge (G_Proof_Ins,
                                         Global_Id'(Kind => Proof_Ins,
                                                    Name => Conditional_Call));

                  Global_Graph.Add_Edge (G_Ins,
                                         Global_Id'(Kind => Inputs,
                                                    Name => Conditional_Call));

                  Global_Graph.Add_Edge (G_Ins,
                                         Global_Id'(Kind => Outputs,
                                                    Name => Conditional_Call));

                  Global_Graph.Add_Edge (G_Outs,
                                         Global_Id'(Kind => Outputs,
                                                    Name => Conditional_Call));
               end loop;
            end;
         end loop;

         --  Add edges between subprograms and variables coming from the
         --  Get_Globals function.
         for N of All_Other_Subprograms loop
            declare
               Subprogram  : constant Entity_Id := Find_Entity (N);

               G_Proof_Ins : constant Global_Id (Proof_Ins) :=
                 (Kind => Proof_Ins,
                  Name => N);

               G_Ins       : constant Global_Id (Inputs) :=
                 (Kind => Inputs,
                  Name => N);

               G_Outs      : constant Global_Id (Outputs) :=
                 (Kind => Outputs,
                  Name => N);

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
               begin
                  for F of FS loop
                     declare
                        Nam : constant Entity_Name :=
                          (if F.Kind in Direct_Mapping | Record_Field
                           then
                              To_Entity_Name (Get_Direct_Mapping_Id (F))
                           elsif F.Kind = Magic_String then
                              F.Name
                           else
                              raise Program_Error);

                        G : constant Global_Id (Variable) :=
                          (Kind => Variable,
                           Name => Nam);

                     begin
                        if not Global_Graph.Edge_Exists (From, G) then
                           Global_Graph.Add_Edge (From, G);
                        end if;
                     end;
                  end loop;
               end Add_Edges_For_FS;

            begin
               if Present (Subprogram) then
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

         --  Close graph, but only add edges that are not in the local graph
         Global_Graph.Conditional_Close (Edge_Selector'Access);

         ----------------------------------------
         -- Create tasking-related call graphs --
         ----------------------------------------

         --  For task ownership checks we create a call graph rooted at
         --  tasks and main-like subprograms. Vertices correspond to callable
         --  entities (i.e. entries, functions and procedures).

         Add_Tasking_Edges : declare
            Stack : Name_Sets.Set;
            --  Subprograms from which we still need to add edges

         begin
            --  First collect tasks and main-like subprograms in SPARK
            for TC in Task_Instances.Iterate loop
               declare
                  S : constant Entity_Name := Task_Instances_Maps.Key (TC);
               begin
                  Stack.Insert (S);
                  Tasking_Call_Graph.Add_Vertex (S);
               end;
            end loop;

            --  Then create a call graph for them
            while not Stack.Is_Empty loop

               declare
                  Caller : constant Entity_Name := Stack (Stack.First);
                  --  Name of the caller

                  V_Caller : constant Entity_Name_Graphs.Vertex_Id :=
                    Tasking_Call_Graph.Get_Vertex (Caller);

                  V_Callee : Entity_Name_Graphs.Vertex_Id;
                  --  Call graph vertices for the caller and the callee

               begin
                  --  If the caller is in SPARK then check its callees;
                  --  otherwise leave it as a leaf of the call graph.

                  --  ??? how about subprogram with SPEC with SPARK_Mode => On,
                  --  but BODY with SPARK_Mode => Off, especially those which
                  --  call another subprogram in its contract?
                  for Callee of Computed_Calls (Caller) loop
                     --  Get vertex for the callee
                     V_Callee := Tasking_Call_Graph.Get_Vertex (Callee);

                     --  If there is no vertex for the callee then create
                     --  one and put the callee on the stack.
                     if V_Callee = Entity_Name_Graphs.Null_Vertex then
                        Tasking_Call_Graph.Add_Vertex (Callee, V_Callee);
                        Stack.Insert (Callee);
                     end if;

                     Tasking_Call_Graph.Add_Edge (V_Caller, V_Callee);
                  end loop;

                  --  Pop the caller from the stack
                  Stack.Delete (Caller);
               end;
            end loop;

            --  Transitive closure
            Tasking_Call_Graph.Close;
         end Add_Tasking_Edges;

         --  To detect potentially blocking operations in protected actions
         --  we create a call graph with vertices corresponding to callable
         --  entities (i.e. entries, functions and procedures).
         --
         --  All edges originate from vertices corresponding to subprograms
         --  in SPARK, since subprograms not in SPARK are considered to be
         --  potentially blocking anyway (they are "leaves" of the call graph).

         Add_Protected_Operation_Edges : declare
            Stack : Name_Sets.Set;
            --  We collect protected operations in SPARK and use them as seeds
            --  to grow the call graph.

            Call_Graph : Entity_Name_Graphs.Graph renames
              Protected_Operation_Call_Graph;

         begin
            --  First collect SPARK-compliant protected operations in the
            --  current compilation unit.
            for E of Marked_Entities loop
               if (Ekind (E) = E_Entry
                   or else (Ekind (E) in E_Function | E_Procedure
                            and then Convention (E) = Convention_Protected))
                 and then Entity_Body_In_SPARK (E)
               then
                  declare
                     E_Name : constant Entity_Name := To_Entity_Name (E);
                  begin
                     Stack.Insert (E_Name);
                     Call_Graph.Add_Vertex (E_Name);
                  end;
               end if;
            end loop;

            --  Then create a call graph for them
            while not Stack.Is_Empty loop

               declare
                  Caller : constant Entity_Name := Stack (Stack.First);
                  --  Name of the caller

                  V_Caller : constant Entity_Name_Graphs.Vertex_Id :=
                    Call_Graph.Get_Vertex (Caller);

                  V_Callee : Entity_Name_Graphs.Vertex_Id;
                  --  Call graph vertices for the caller and the callee

               begin
                  --  If the caller is nonblocking then check its callees;
                  --  otherwise leave it as a leaf of the call graph.
                  if Nonblocking_Subprograms.Contains (Caller) then
                     for Callee of Computed_Calls (Caller) loop
                        --  Get vertex for the callee
                        V_Callee := Call_Graph.Get_Vertex (Callee);

                        --  If there is no vertex for the callee then create
                        --  one and put the callee on the stack.
                        if V_Callee = Entity_Name_Graphs.Null_Vertex then
                           Call_Graph.Add_Vertex (Callee, V_Callee);
                           Stack.Insert (Callee);
                        end if;

                        Call_Graph.Add_Edge (V_Caller, V_Callee);
                     end loop;
                  end if;

                  --  Pop the caller from the stack
                  Stack.Delete (Caller);
               end;
            end loop;

            --  Close the call graph; for an empty graph it will be a no-op
            Call_Graph.Close;
         end Add_Protected_Operation_Edges;

         Add_Ceiling_Priority_Edges : declare
            Stack : Name_Sets.Set;
            --  We collect protected operations in SPARK and use them as seeds
            --  to grow the call graph.

            Call_Graph : Entity_Name_Graphs.Graph renames
              Ceiling_Priority_Call_Graph;

         begin
            --  First collect SPARK-compliant protected operations, task types
            --  and main-like subprograms in the current compilation unit.
            for E of Marked_Entities loop
               if (case Ekind (E) is
                      when E_Entry | E_Task_Type =>
                         True,
                      when E_Function | E_Procedure =>
                         Convention (E) = Convention_Protected
                         or else Might_Be_Main (E),
                      when others =>
                         False)
                 and then Entity_Body_In_SPARK (E)
                 and then Analysis_Requested (E, With_Inlined => True)
               then
                  declare
                     E_Name : constant Entity_Name := To_Entity_Name (E);
                  begin
                     Stack.Insert (E_Name);
                     Call_Graph.Add_Vertex (E_Name);
                  end;
               end if;
            end loop;

            --  Then create a call graph for them
            while not Stack.Is_Empty loop

               declare
                  Caller : constant Entity_Name := Stack (Stack.First);
                  --  Name of the caller

                  V_Caller : constant Entity_Name_Graphs.Vertex_Id :=
                    Call_Graph.Get_Vertex (Caller);

                  V_Callee : Entity_Name_Graphs.Vertex_Id;
                  --  Call graph vertices for the caller and the callee

               begin
                  for Callee of Computed_Calls (Caller) loop
                     --  Get vertex for the callee
                     V_Callee := Call_Graph.Get_Vertex (Callee);

                     --  If there is no vertex for the callee then create
                     --  one and put the callee on the stack.
                     if V_Callee = Entity_Name_Graphs.Null_Vertex then
                        Call_Graph.Add_Vertex (Callee, V_Callee);

                        --  If the callee is a protected subprogram or entry
                        --  then do not put it on the stack; if its analysis is
                        --  requested then it is already a root of the graph.
                        if not Is_Protected_Operation (Callee) then
                           Stack.Include (Callee);
                        end if;

                     end if;

                     Call_Graph.Add_Edge (V_Caller, V_Callee);

                  end loop;

                  --  Pop the caller from the stack
                  Stack.Delete (Caller);
               end;
            end loop;

            Call_Graph.Close;
         end Add_Ceiling_Priority_Edges;
      end Add_All_Edges;

      -------------------------
      -- Create_All_Vertices --
      -------------------------

      procedure Create_All_Vertices is
         use Global_Graphs;
      begin
         --  Create vertices for all global variables
         for N of All_Globals loop
            Global_Graph.Add_Vertex (Global_Id'(Kind => Variable,
                                                Name => N));
         end loop;

         --  Create Ins, Outs and Proof_Ins vertices for all subprograms
         for Subprogram_Name of All_Subprograms loop
            for K in Inputs .. Proof_Ins loop
               declare
                  G : Global_Id (K);
                  --  This should really be a constant, but its initialization
                  --  would require the use of non-static discriminant.
               begin
                  G.Name := Subprogram_Name;
                  Global_Graph.Add_Vertex (G);
               end;
            end loop;
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
               --  Creates a vertex for every Flow_Id in FS that does not
               --  already have one.

               ----------------------------
               -- Create_Vertices_For_FS --
               ----------------------------

               procedure Create_Vertices_For_FS (FS : Flow_Id_Sets.Set) is
                  G   : Global_Id (Variable);
                  Nam : Entity_Name;
               begin
                  for F of FS loop
                     Nam := (if F.Kind in Direct_Mapping | Record_Field then
                                To_Entity_Name (Get_Direct_Mapping_Id (F))
                             elsif F.Kind = Magic_String then
                                F.Name
                             else
                                raise Program_Error);
                     G   := Global_Id'(Kind => Variable,
                                       Name => Nam);

                     if not Global_Graph.Contains (G) then
                        Global_Graph.Add_Vertex (G);
                     end if;
                  end loop;
               end Create_Vertices_For_FS;

            begin
               if Present (Subprogram) then
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
         use Global_Graphs;

         G_Subp       : Global_Id (Subprogram);
         G_Local_Subp : Global_Id (Subprogram);
         G_Local_Var  : Global_Id (Variable);

      --  Start of processing for Create_Local_Graph

      begin
         for Info of Subprogram_Info_List loop
            G_Subp := Global_Id'(Kind => Subprogram,
                                 Name => Info.Name);

            if not Local_Graph.Contains (G_Subp) then
               --  Create a vertex for the subprogram if one does not already
               --  exist.
               Local_Graph.Add_Vertex (G_Subp);
            end if;

            --  Create a vertex for every local variable and link it to the
            --  enclosing subprogram.
            for Local_Variable of Info.Local_Variables loop
               G_Local_Var := Global_Id'(Kind => Variable,
                                         Name => Local_Variable);

               --  Create a vertex for every local variable if one does not
               --  already exist.
               if not Local_Graph.Contains (G_Local_Var) then
                  Local_Graph.Add_Vertex (G_Local_Var);
               end if;

               --  Link enclosing subprogram to local variable
               Local_Graph.Add_Edge (G_Subp, G_Local_Var);
            end loop;

            --  Create a vertex for every local subprogram and link it to the
            --  enclosing subprogram.
            for Local_Subprogram of Info.Local_Subprograms loop
               G_Local_Subp := Global_Id'(Kind => Subprogram,
                                          Name => Local_Subprogram);

               if not Local_Graph.Contains (G_Local_Subp) then
                  --  Create a vertex for every local subprogram if one does
                  --  not already exist.
                  Local_Graph.Add_Vertex (G_Local_Subp);
               end if;

               --  Link enclosing subprogram to local subprogram
               Local_Graph.Add_Edge (G_Subp, G_Local_Subp);
            end loop;

            --  Link all local variables to all local subprograms (this
            --  effectively means that they can act as their globals).
            for Local_Variable of Info.Local_Variables loop
               G_Local_Var := Global_Id'(Kind => Variable,
                                         Name => Local_Variable);

               for Local_Subprogram of Info.Local_Subprograms loop
                  G_Local_Subp := Global_Id'(Kind => Subprogram,
                                             Name => Local_Subprogram);

                  Local_Graph.Add_Edge (G_Local_Var, G_Local_Subp);
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
         use Global_Graphs;

         function Get_Variable_Neighbours
           (Start : Vertex_Id)
            return Vertex_Sets.Set;
         --  Returns a set of all Neighbours of Start that correspond to
         --  variables.

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
               if Global_Graph.Get_Key (V).Kind = Variable then
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
                 Global_Id'(Kind => Inputs,
                            Name => Info.Name);

               G_Outs      : constant Global_Id :=
                 Global_Id'(Kind => Outputs,
                            Name => Info.Name);

               G_Proof_Ins : constant Global_Id :=
                 Global_Id'(Kind => Proof_Ins,
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
                        Global_Graph.Add_Edge (V_Ins, V);
                     end if;

                     Global_Graph.Remove_Edge (V_Proof_Ins, V);
                  end if;
               end loop;
            end;
         end loop;
      end Edit_Proof_Ins;

      ----------------------------------
      -- Generate_Initializes_Aspects --
      ----------------------------------

      procedure Generate_Initializes_Aspects is
      begin
         for P of Package_Info_List loop
            declare
               II        : Initializes_Info;
               --  The new name dependency map for package P

               LHS       : Name_Sets.Set := Name_Sets.Empty_Set;
               LHS_Proof : Name_Sets.Set := Name_Sets.Empty_Set;
               --  LHS and LHS_Proof combined will represent the left hand side
               --  of the generated initializes aspect.

               RHS       : Name_Sets.Set := P.Inputs;
               RHS_Proof : Name_Sets.Set := P.Inputs_Proof;
               --  RHS and RHS_Proof combined will represent the right
               --  hand side of the generated initializes aspect; they
               --  are initialized with package inputs and proof inputs,
               --  respectively.

               LV        : Name_Sets.Set := Name_Sets.Empty_Set;
               LV_Proof  : Name_Sets.Set := Name_Sets.Empty_Set;
               --  Flow id sets of local variables/states and local proof
               --  variables/states.

               ODC       : Name_Sets.Set := Name_Sets.Empty_Set;
               --  Outputs of Definite Calls

               procedure Add_To_Proof_Or_Normal_Set
                 (EN         : Entity_Name;
                  Proof_Set  : in out Name_Sets.Set;
                  Normal_Set : in out Name_Sets.Set);
               --  Adds EN to either Proof_Set or Normal_Set depending on
               --  whether it is a ghost entity or not.

               --------------------------------
               -- Add_To_Proof_Or_Normal_Set --
               --------------------------------

               procedure Add_To_Proof_Or_Normal_Set
                 (EN         : Entity_Name;
                  Proof_Set  : in out Name_Sets.Set;
                  Normal_Set : in out Name_Sets.Set)
               is
                  E : constant Entity_Id := Find_Entity (EN);
               begin
                  if Present (E)
                    and then Is_Ghost_Entity (E)
                  then
                     Proof_Set.Insert (EN);
                  else
                     Normal_Set.Insert (EN);
                  end if;
               end Add_To_Proof_Or_Normal_Set;

            --  Start of processing for Generate_Initializes_Aspects

            begin
               --  Add local variables to either LV_Proof or LV depending on
               --  whether they are ghosts or not.
               for Local_Variable of P.Local_Variables loop
                  Add_To_Proof_Or_Normal_Set (Local_Variable,
                                              LV_Proof,
                                              LV);

                  --  Add local state abstractions with null refinements to the
                  --  list of local definite writes since they are trivially
                  --  initialized.
                  declare
                     Local_State : constant Name_Graphs.Cursor :=
                       State_Comp_Map.Find (Local_Variable);
                  begin
                     if Name_Graphs.Has_Element (Local_State)
                       and then State_Comp_Map (Local_State).Is_Empty
                     then
                        Add_To_Proof_Or_Normal_Set (Local_Variable,
                                                    LHS_Proof,
                                                    LHS);
                     end if;
                  end;
               end loop;

               --  Add definite local writes to either LHS_Proof or LHS
               --  depending on whether they are ghosts or not.
               for Local_Definite_Write of P.Local_Definite_Writes loop
                  Add_To_Proof_Or_Normal_Set (Local_Definite_Write,
                                              LHS_Proof,
                                              LHS);
               end loop;

               --  Add the intersection of pure outputs (outputs that are not
               --  also read) of definite calls and local variables to LHS.
               --  Additionally, add Reads and Proof_Reads of definite calls
               --  to RHS and RHS_Proof respectively.
               for Definite_Call of P.Definite_Calls loop
                  declare
                     Proof_Reads : Name_Sets.Set;
                     Reads       : Name_Sets.Set;
                     Writes      : Name_Sets.Set;
                  begin
                     if GG_Exists_Cache.Contains (Definite_Call) then
                        GG_Get_MR_Globals (EN          => Definite_Call,
                                           Proof_Reads => Proof_Reads,
                                           Reads       => Reads,
                                           Writes      => Writes);

                        RHS_Proof.Union (Proof_Reads);
                        RHS.Union (Reads);
                        ODC.Union (Writes - Reads);
                     end if;
                  end;
               end loop;
               LHS.Union (LV and ODC);

               --  Add Reads and Writes of conditional calls to the RHS set and
               --  their Proof_Reads to the RHS_Proof set.
               for Conditional_Call of P.Conditional_Calls loop
                  declare
                     Proof_Reads : Name_Sets.Set;
                     Reads       : Name_Sets.Set;
                     Writes      : Name_Sets.Set;
                  begin
                     if GG_Exists_Cache.Contains (Conditional_Call) then
                        GG_Get_MR_Globals (EN          => Conditional_Call,
                                           Proof_Reads => Proof_Reads,
                                           Reads       => Reads,
                                           Writes      => Writes);

                        RHS_Proof.Union (Proof_Reads);
                        RHS.Union (Reads);
                        RHS.Union (Writes);
                     end if;
                  end;
               end loop;

               --  Remove local variables from the sets since they should not
               --  appear in Initializes aspects.
               RHS.Difference (P.Local_Variables);
               RHS_Proof.Difference (P.Local_Variables);

               --  Assign II
               II := (LHS       => LHS,
                      LHS_Proof => LHS_Proof,
                      RHS       => RHS,
                      RHS_Proof => RHS_Proof);

               --  Add LHS and LHS_Proof to the All_Initialized_Names set
               All_Initialized_Names.Union (II.LHS);
               All_Initialized_Names.Union (II.LHS_Proof);

               --  Add state abstractions to the All_Initialized_Names set when
               --  all constituents are initialized and remove constituents of
               --  state abstractions that are not fully initialized.
               declare
                  All_LHS   : constant Name_Sets.Set := LHS or LHS_Proof;
                  State     : Any_Entity_Name;
                  To_Remove : Name_Sets.Set := Name_Sets.Empty_Set;
               begin
                  for Var of All_LHS loop
                     State := GG_Enclosing_State (Var);

                     if State /= Null_Entity_Name then
                        if (for all Const of State_Comp_Map (State)
                              => All_LHS.Contains (Const))
                        then
                           --  All constituents are initialized so we add the
                           --  entire abstract state.
                           All_Initialized_Names.Include (State);
                        else
                           --  At least one constituent is not initialized so
                           --  there is no point in considering the current
                           --  constituent alone as being initialized.
                           To_Remove.Insert (Var);
                        end if;
                     end if;
                  end loop;

                  --  Remove constituents whose enclosing state abstraction is
                  --  not fully initialized.
                  All_Initialized_Names.Difference (To_Remove);
                  II.LHS.Difference (To_Remove);
                  II.LHS_Proof.Difference (To_Remove);
               end;

               --  Insert II into Initializes_Aspects_Map
               Initializes_Aspects_Map.Insert (P.Name, II);

            end;

            --  This is a convenient place to populate the
            --  Package_To_Locals_Map.
            Package_To_Locals_Map.Insert (P.Name, P.Local_Variables);
         end loop;

         if Debug_Print_Generated_Initializes then
            Print_Generated_Initializes_Aspects;
         end if;
      end Generate_Initializes_Aspects;

      ---------------------------
      -- Load_GG_Info_From_ALI --
      ---------------------------

      procedure Load_GG_Info_From_ALI (ALI_File_Name : File_Name_Type) is
         ALI_File_Name_Str : constant String :=
           Get_Name_String (Full_Lib_File_Name (ALI_File_Name));

         Sanitized_Name : constant String :=
           To_String (Trim (Source => To_Unbounded_String (ALI_File_Name_Str),
                            Left   => Null_Set,
                            Right  => To_Set (Character'Val (0))));

         procedure Issue_Corrupted_File_Error (Msg : String)
         with No_Return;
         --  Issues an error about the ALI file being corrupted and suggests
         --  the usage of "gnatprove --clean".

         --------------------------------
         -- Issue_Corrupted_File_Error --
         --------------------------------

         procedure Issue_Corrupted_File_Error (Msg : String) is
         begin
            Abort_With_Message
              ("Corrupted ali file detected (" & Sanitized_Name & "): " &
                 Msg &
                 ". Call gnatprove with ""--clean"".");
         end Issue_Corrupted_File_Error;

         ALI_File  : Ada.Text_IO.File_Type;
         Line      : Unbounded_String;

         Found_End     : Boolean := False;
         Found_Version : Boolean := False;
         --  This will be set to True once we find the end marker

      --  Start of processing for Load_GG_Info_From_ALI

      begin
         Open (ALI_File, In_File, ALI_File_Name_Str);

         --  Skip to the version section
         loop
            if End_Of_File (ALI_File) then
               Close (ALI_File);
               return;
            end if;

            Get_Line (ALI_File, Line);
            if Length (Line) >= 3 then
               declare
                  Header : constant String (1 .. 3) := Slice (Line, 1, 3);

               begin
                  if Header = "QQ " then
                     Found_Version := To_String (Line) = "QQ SPARKVERSION " &
                       SPARK2014_Static_Version_String;
                     exit;
                  elsif Header = "GG " then
                     --  We have encountered a GG section without the spark
                     --  version marker. This indicates an older spark version.
                     exit;
                  end if;
               end;
            end if;
         end loop;

         if not Found_Version then
            Issue_Corrupted_File_Error ("inconsistent spark version");
         end if;

         --  Now skip to the GG section
         loop
            if End_Of_File (ALI_File) then
               Close (ALI_File);
               return;
            end if;

            Get_Line (ALI_File, Line);
            exit when Length (Line) >= 3 and then Slice (Line, 1, 3) = "GG ";
         end loop;

         --  We have reached the "GG" section of the ALI file
         while Length (Line) >= 5 and then Slice (Line, 1, 3) = "GG " loop
            --  Parse the given record.
            declare
               A : Archive (Serialisation.Input) :=
                 From_String (Unbounded_Slice (Line, 4, Length (Line)));
               V : ALI_Entry := (Kind => EK_Error);
            begin
               Serialize (A, V);
               case V.Kind is
                  when EK_Error =>
                     Issue_Corrupted_File_Error ("parse error");

                  when EK_End_Marker =>
                     Found_End := True;
                     exit;

                  when EK_State_Map =>
                     declare
                        State    : Name_Graphs.Cursor;
                        Inserted : Boolean;

                        C : Name_Lists.Cursor;
                        --  Cursor to iterate over original constituents; it is
                        --  required because it is not possible to iterate over
                        --  a component of a discriminated record.

                     begin
                        State_Comp_Map.Insert (Key      => V.The_State,
                                               Position => State,
                                               Inserted => Inserted);
                        pragma Assert (Inserted);

                        C := V.The_Constituents.First;
                        while Name_Lists.Has_Element (C) loop
                           State_Comp_Map (State).Insert
                             (V.The_Constituents (C));
                           Name_Lists.Next (C);
                        end loop;
                     end;

                     State_Abstractions.Include (V.The_State);

                  when EK_Remote_States =>
                     State_Abstractions.Union (V.Remote_States);

                  when EK_Volatiles =>
                     Async_Writers_Vars.Union (V.All_Async_Writers);
                     All_Volatile_Vars.Union (V.All_Async_Writers);

                     Async_Readers_Vars.Union (V.All_Async_Readers);
                     All_Volatile_Vars.Union (V.All_Async_Readers);

                     Effective_Reads_Vars.Union (V.All_Effective_Reads);
                     All_Volatile_Vars.Union (V.All_Effective_Reads);

                     Effective_Writes_Vars.Union (V.All_Effective_Writes);
                     All_Volatile_Vars.Union (V.All_Effective_Writes);

                  when EK_Globals =>
                     All_Globals.Union (V.The_Global_Info.Inputs_Proof);
                     All_Globals.Union (V.The_Global_Info.Inputs);
                     All_Globals.Union (V.The_Global_Info.Outputs);

                     All_Subprograms.Union (V.The_Global_Info.Proof_Calls);
                     All_Subprograms.Union (V.The_Global_Info.Definite_Calls);
                     All_Subprograms.Union
                       (V.The_Global_Info.Conditional_Calls);

                     All_Globals.Union (V.The_Global_Info.Local_Variables);
                     All_Subprograms.Union
                       (V.The_Global_Info.Local_Subprograms);
                     All_Globals.Union
                       (V.The_Global_Info.Local_Definite_Writes);

                     case V.The_Global_Info.Kind is
                        when Kind_Subprogram | Kind_Entry | Kind_Task =>
                           GG_Subprograms.Include (V.The_Global_Info.Name);
                           All_Subprograms.Include (V.The_Global_Info.Name);

                           Subprogram_Info_List.Append (V.The_Global_Info);

                        when Kind_Package | Kind_Package_Body =>
                           Package_Info_List.Append (V.The_Global_Info);
                     end case;

                     GG_Exists_Cache.Insert (V.The_Global_Info.Name);

                  when EK_Protected_Instance =>
                     declare
                        C : Entity_Name_To_Priorities_Maps.Cursor;
                        --  Position of a list of protected components of a
                        --  global variable and their priorities.

                        Dummy : Boolean;
                        --  Flag that indicates if a key was inserted or if
                        --  it already existed in a map. It is required by
                        --  the hashed-maps API, but not used here.

                     begin
                        --  Find a list of protected components of a global
                        --  variable; if it does not exist then initialize
                        --  with an empty list.
                        Protected_Objects.Insert
                          (Key      => V.The_Variable,
                           Position => C,
                           Inserted => Dummy);

                        Protected_Objects (C).Append (V.The_Priority);
                     end;

                  when EK_Task_Instance =>
                     Register_Task_Object (V.The_Type, V.The_Object);

                  when EK_Tasking_Info =>
                     for Kind in Tasking_Info_Kind loop
                        if not V.The_Tasking_Info (Kind).Is_Empty then
                           Tasking_Info_Bag (GG_Phase_1, Kind).Insert
                             (V.The_Entity,
                              V.The_Tasking_Info (Kind));
                        end if;
                     end loop;

                  when EK_Nonblocking =>
                     declare
                        C : Name_Lists.Cursor :=
                          V.The_Nonblocking_Subprograms.First;
                     begin
                        while Name_Lists.Has_Element (C) loop
                           Nonblocking_Subprograms.Insert
                             (V.The_Nonblocking_Subprograms (C));

                           Name_Lists.Next (C);
                        end loop;
                     end;
               end case;
            end;

            exit when End_Of_File (ALI_File);

            --  Proceed to the next line.
            Get_Line (ALI_File, Line);
         end loop;

         if not Found_End then
            --  If we have not found the end marker by now, the file is
            --  broken...
            Issue_Corrupted_File_Error ("missing end marker");
         end if;

         Close (ALI_File);
      end Load_GG_Info_From_ALI;

      ---------------
      -- Note_Time --
      ---------------

      procedure Note_Time (Message : String) is
      begin
         if Debug_GG_Read_Timing then
            Flow_Debug.Note_Time (Message);
         end if;
      end Note_Time;

      ---------------------------
      -- Process_Tasking_Graph --
      ---------------------------

      procedure Process_Tasking_Graph is
         use Entity_Name_Graphs;
         G : Entity_Name_Graphs.Graph := Tasking_Call_Graph;
      begin
         --  Do the transitive closure
         G.Close;

         --  Collect information for each main-like subprogram
         for TC in Task_Instances.Iterate loop
            declare
               TN : constant Entity_Name := Task_Instances_Maps.Key (TC);
               --  Name of task or main-like subprogram

               TV : constant Vertex_Id := Tasking_Call_Graph.Get_Vertex (TN);
               --  Corresponding vertex in tasking call graph

               procedure Collect_From (S : Entity_Name);
               --  Collect tasking objects accessed by subprogram S as if they
               --  were accessed by task TN.

               ------------------
               -- Collect_From --
               ------------------

               procedure Collect_From (S : Entity_Name) is
               begin
                  for Kind in Tasking_Info_Kind loop
                     declare

                        Phase_1_Info : Name_Graphs.Map renames
                          Tasking_Info_Bag (GG_Phase_1, Kind);

                        S_C : constant Name_Graphs.Cursor :=
                          Phase_1_Info.Find (S);
                        --  Pointer to objects accessed by subprogram S

                        T_C : Name_Graphs.Cursor;
                        --  Pointer to objects accessed by task T

                        Inserted : Boolean;
                        --  Flag that indicates if a key was inserted or if
                        --  it already existed in a map. It is required by
                        --  the hashed-maps API, but not used here.

                     begin
                        --  Only do something if S accesses any objects
                        if Name_Graphs.Has_Element (S_C) then
                           Tasking_Info_Bag (GG_Phase_2, Kind).Insert
                             (Key      => TN,
                              Position => T_C,
                              Inserted => Inserted);

                           Tasking_Info_Bag (GG_Phase_2, Kind) (T_C).Union
                             (Phase_1_Info (S_C));
                        end if;
                     end;
                  end loop;
               end Collect_From;

            begin

               --  Now graph G is a transitive (but not reflexive!) closure.
               --  We need to explicitly collect objects accessed by the task
               --  itself, and then all subprogram called it calls (directly
               --  or indirectly).

               Collect_From (TN);
               for SV of G.Get_Collection (TV, Out_Neighbours) loop
                  declare
                     S : constant Entity_Name := G.Get_Key (SV);
                  begin
                     Collect_From (S);
                  end;
               end loop;
            end;
         end loop;
      end Process_Tasking_Graph;

      ---------------------------------------------
      -- Remove_Constants_Without_Variable_Input --
      ---------------------------------------------

      procedure Remove_Constants_Without_Variable_Input is
         use Global_Graphs;

      begin
         --  Detect constants without variable input
         for Glob of All_Globals loop
            declare
               Const : constant Entity_Id := Find_Entity (Glob);
            begin
               if Present (Const)
                 and then Ekind (Const) = E_Constant
                 and then not Has_Variable_Input (Direct_Mapping_Id (Const))
               then
                  --  Remove all edges going in and out of a constant without
                  --  variable input.
                  declare
                     Const_G_Id : constant Global_Id :=
                       Global_Id'(Kind => Variable,
                                  Name => Glob);

                     Const_V    : constant Vertex_Id :=
                       Global_Graph.Get_Vertex (Const_G_Id);
                  begin
                     Global_Graph.Clear_Vertex (Const_V);
                  end;
               end if;
            end;
         end loop;
      end Remove_Constants_Without_Variable_Input;

   --  Start of processing for GG_Read

   begin
      Current_Comp_Unit := GNAT_Root;
      Current_Mode      := GG_Read_Mode;

      if Debug_GG_Read_Timing then
         Init_Time ("gg_read");
      end if;

      --  Initialize volatile info
      All_Volatile_Vars     := Name_Sets.Empty_Set;
      Async_Writers_Vars    := Name_Sets.Empty_Set;
      Async_Readers_Vars    := Name_Sets.Empty_Set;
      Effective_Reads_Vars  := Name_Sets.Empty_Set;
      Effective_Writes_Vars := Name_Sets.Empty_Set;

      --  Go through all ALI files and populate the Subprogram_Info_List
      declare
         Read_Files : String_Sets.Set;
         Nam        : Unbounded_String;

         Inserted : Boolean;
         Dummy    : String_Sets.Cursor;
      begin
         for Index in ALIs.First .. ALIs.Last loop
            --  ??? The ALI table seems to incldue some entries twice, but that
            --  is because some of them are null-terminated. See O714-006; this
            --  is the workaround for now.
            Nam := To_Unbounded_String
              (Get_Name_String (Full_Lib_File_Name
               (ALIs.Table (Index).Afile)));
            Nam := Trim (Source => Nam,
                         Left   => Null_Set,
                         Right  => To_Set (Character'Val (0)));

            Read_Files.Insert (New_Item => To_String (Nam),
                               Position => Dummy,
                               Inserted => Inserted);

            if Inserted then
               Load_GG_Info_From_ALI (ALIs.Table (Index).Afile);
            end if;
         end loop;
      end;

      Note_Time ("gg_read - ALI files read");

      if Debug_Print_Info_Sets_Read then
         --  Print all GG related info gathered from the ALI files
         for Info of Subprogram_Info_List loop
            Write_Eol;
            Print_Global_Phase_1_Info (Info);
         end loop;

         for C in State_Comp_Map.Iterate loop
            declare
               State        : Entity_Name   renames Key (C);
               Constituents : Name_Sets.Set renames State_Comp_Map (C);
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
      Note_Time ("gg_read - local graph done");

      --  Create all vertices of the Global_Graph
      Create_All_Vertices;
      Note_Time ("gg_read - vertices added");

      --  If it is a library-level subprogram with no parameters then it may
      --  be the main subprogram of a partition and thus be executed by the
      --  environment task.
      --
      --  Such a subprogram might be given either as a spec, body or instance
      --  of a generic procedure, in which case front end wraps it inside
      --  a package body. Currently GNAT does not allow subprogram renaming
      --  to be main, but this choice is implementation-specific (see AA RM
      --  10.2(29.b)).
      --
      --  The following code mirrors front end tests in
      --  Lib.Writ.Write_ALI.Output_Main_Program_Line, but also detects
      --  main-like subprogram declaration, which we want to analyze even if
      --  there is yet no a subprogram body or it is not in SPARK.

      Detect_Main_Subprogram : declare
         U : constant Node_Id := Unit (GNAT_Root);
         S : Node_Id;

      begin
         case Nkind (U) is
            when N_Subprogram_Body =>
               S := (if Acts_As_Spec (U)
                     then Defining_Unit_Name (Specification (U))
                     else Corresponding_Spec (U));

            when N_Subprogram_Declaration =>
               S := Defining_Unit_Name (Specification (U));

            when N_Package_Body =>
               if Nkind (Original_Node (U)) in N_Subprogram_Instantiation then

                  S := Alias (Related_Instance
                            (Defining_Unit_Name (Specification
                               (Unit (Library_Unit (GNAT_Root))))));

                  --  ??? A generic subprogram is never a main program
                  --  ??? If it is a child unit, get its simple name
               else
                  S := Empty;
               end if;

            when others =>
               S := Empty;

         end case;

         if Present (S) and then Might_Be_Main (S) then
            declare
               Main_Entity_Name : constant Entity_Name := To_Entity_Name (S);
            begin
               Register_Task_Object (Type_Name => Main_Entity_Name,
                                     Object    =>
                                       (Name      => Main_Entity_Name,
                                        Instances => One,
                                        Node      => S));
               --  Register the main-like subprogram as a task, but use the
               --  same entity name for type and object name.
            end;
         end if;

      end Detect_Main_Subprogram;

      --  Add all edges in the Global_Graph and tasking-related graphs
      Add_All_Edges;
      Note_Time ("gg_read - edges added");

      --  Edit Proof_Ins
      Edit_Proof_Ins;
      Note_Time ("gg_read - proof ins");

      --  Put tasking-related information back to the bag
      Process_Tasking_Graph;
      Print_Tasking_Info_Bag (GG_Phase_2);

      --  Now that the Globals Graph has been generated we set GG_Generated to
      --  True. Notice that we set GG_Generated to True before we remove edges
      --  leading to constants without variable input. The reasoning behind
      --  this is to use the generated globals instead of the computed globals
      --  when we call Get_Globals from within Has_Variable_Input.
      GG_Generated := True;

      --  Remove edges leading to constants which do not have variable input
      Remove_Constants_Without_Variable_Input;
      Note_Time ("gg_read - removed nonvariable constants");

      if Debug_Print_Global_Graph then
         declare
            Common_Prefix : constant String :=
              Spec_File_Name_Without_Suffix
                (Enclosing_Comp_Unit_Node (GNAT_Root));

            Local_Filename   : constant String :=
              Common_Prefix & "_locals_graph";

            Global_Filename   : constant String :=
              Common_Prefix & "_globals_graph";
         begin
            Print_Global_Graph (Filename => Local_Filename,
                                G        => Local_Graph);

            Print_Global_Graph (Filename => Global_Filename,
                                G        => Global_Graph);
         end;
      end if;

      --  To speed up queries on constituents of state, we fill in a helper
      --  structure.
      Comp_State_Map := Name_Maps.Empty_Map;
      for C in State_Comp_Map.Iterate loop
         for Comp of State_Comp_Map (C) loop
            Comp_State_Map.Insert (Comp, Key (C));
         end loop;
      end loop;

      --  Now that the globals are generated, we use them to also generate the
      --  initializes aspects.
      Generate_Initializes_Aspects;

      if Debug_GG_Read_Timing then
         Final_Time ("gg_read");
      end if;

   end GG_Read;

   --------------------------------------------------------------------------
   --  Queries
   --------------------------------------------------------------------------

   --------------------------
   -- Component_Priorities --
   --------------------------

   function Component_Priorities
     (Obj : Entity_Name)
      return Object_Priority_Lists.List
      renames Protected_Objects.Element;

   ---------------------------------------
   -- Directly_Called_Protected_Objects --
   ---------------------------------------

   function Directly_Called_Protected_Objects
     (Ent : Entity_Name) return Name_Sets.Set
   is
      use Entity_Name_Graphs;

      Call_Graph : Entity_Name_Graphs.Graph renames
        Ceiling_Priority_Call_Graph;

      Res : Name_Sets.Set;
      V   : constant Vertex_Id := Call_Graph.Get_Vertex (Ent);

      procedure Collect_Objects_From_Subprogram (S : Entity_Name);
      --  Collect protected objects directly accessed from subprogram S

      -------------------------------------
      -- Collect_Objects_From_Subprogram --
      -------------------------------------

      procedure Collect_Objects_From_Subprogram (S : Entity_Name) is

         subtype Protected_Info_Kind is Tasking_Info_Kind with
           Static_Predicate =>
             Protected_Info_Kind in Entry_Calls | Write_Locks | Read_Locks;
         --  Accesses to protected objects that trigger ceiling priority checks

      begin
         for Kind in Protected_Info_Kind loop
            declare
               Phase_1_Info : Name_Graphs.Map renames
                 Tasking_Info_Bag (GG_Phase_1, Kind);

               C : constant Name_Graphs.Cursor := Phase_1_Info.Find (S);

            begin
               if Has_Element (C) then
                  Res.Union (Phase_1_Info (C));
               end if;
            end;
         end loop;
      end Collect_Objects_From_Subprogram;

   --  Start of processing for Directly_Called_Protected_Objects

   begin
      --  Vertex V might be null if we only have a spec for entity Ent
      if V /= Null_Vertex then
         --  Collect objects from the caller subprogram it self
         Collect_Objects_From_Subprogram (Ent);

         --  and from all its callees
         for Obj of Call_Graph.Get_Collection (V, Out_Neighbours) loop
            declare
               Callee : constant Entity_Name := Call_Graph.Get_Key (Obj);
            begin
               Collect_Objects_From_Subprogram (Callee);
            end;
         end loop;
      end if;

      return Res;
   end Directly_Called_Protected_Objects;

   ------------------------
   -- GG_Enclosing_State --
   ------------------------

   function GG_Enclosing_State (EN : Entity_Name) return Any_Entity_Name is
      C : constant Name_Maps.Cursor := Comp_State_Map.Find (EN);
      use Name_Maps;
   begin
      return (if Has_Element (C)
              then Element (C)
              else Null_Entity_Name);
   end GG_Enclosing_State;

   --------------
   -- GG_Exist --
   --------------

   function GG_Exist (E : Entity_Id) return Boolean is
      Name : constant Entity_Name := To_Entity_Name (E);
   begin
      return GG_Exists_Cache.Contains (Name);
   end GG_Exist;

   ---------------------------
   -- GG_Has_Been_Generated --
   ---------------------------

   function GG_Has_Been_Generated return Boolean is (GG_Generated);
   --  @return True iff the Global Graph has been generated

   --------------------------
   -- GG_Has_Async_Readers --
   --------------------------

   function GG_Has_Async_Readers (EN : Entity_Name) return Boolean
     renames Async_Readers_Vars.Contains;

   --------------------------
   -- GG_Has_Async_Writers --
   --------------------------

   function GG_Has_Async_Writers (EN : Entity_Name) return Boolean
     renames Async_Writers_Vars.Contains;

   ----------------------------
   -- GG_Has_Effective_Reads --
   ----------------------------

   function GG_Has_Effective_Reads (EN : Entity_Name) return Boolean
     renames Effective_Reads_Vars.Contains;

   -----------------------------
   -- GG_Has_Effective_Writes --
   -----------------------------

   function GG_Has_Effective_Writes (EN : Entity_Name) return Boolean
     renames Effective_Writes_Vars.Contains;

   -----------------------
   -- GG_Is_Constituent --
   -----------------------

   function GG_Is_Constituent (EN : Entity_Name) return Boolean
     renames Comp_State_Map.Contains;

   --------------------------------------
   -- GG_Is_Initialized_At_Elaboration --
   --------------------------------------

   function GG_Is_Initialized_At_Elaboration
     (EN : Entity_Name)
      return Boolean is
     (All_Initialized_Names.Contains (EN)
        or else GG_Has_Async_Writers (EN));

   --------------------
   -- GG_Is_Volatile --
   --------------------

   function GG_Is_Volatile (EN : Entity_Name) return Boolean
     renames All_Volatile_Vars.Contains;

   -----------------------------
   -- Is_Potentially_Blocking --
   -----------------------------

   function Is_Potentially_Blocking (E : Entity_Id) return Boolean is
      EN : constant Entity_Name := To_Entity_Name (E);
      --  Entity name

      Protected_Type_E : constant Entity_Id := Scope (E);
      --  Entity of the enclosing protected type

      function Calls_Potentially_Blocking_Subprogram return Boolean;
      --  Check for calls to potentially blocking subprograms of a given Kind

      -------------------------------------------
      -- Calls_Potentially_Blocking_Subprogram --
      -------------------------------------------

      function Calls_Potentially_Blocking_Subprogram return Boolean is
         use Entity_Name_Graphs;

         Caller : constant Vertex_Id :=
           Protected_Operation_Call_Graph.Get_Vertex (EN);
         --  Vertex that represents the analysed subprogram

         function Calls_Same_Target_Type (S : Entity_Name) return Boolean;
         --  Check if subprogram S calls the enclosing protected type of E

         function Is_Predefined (Subprogram : String) return Boolean;
         --  Check if Subprogram is in a unit predefined by the Ada RM

         ----------------------------
         -- Calls_Same_Target_Type --
         ----------------------------

         function Calls_Same_Target_Type (S : Entity_Name) return Boolean is
            Subp_V : constant Vertex_Id :=
              Protected_Operation_Call_Graph.Get_Vertex (S);
            --  Vertex that represents subprogram S

         begin
            --  Iterate over subprograms called by subprogram S
            for V of Protected_Operation_Call_Graph.
              Get_Collection (Subp_V, Out_Neighbours)
            loop
               declare
                  Callee : constant Entity_Name :=
                    Protected_Operation_Call_Graph.Get_Key (V);
                  --  Vertex that represent subprogram called by S

                  Callee_E : constant Entity_Id := Find_Entity (Callee);
               begin
                  if Present (Callee_E)
                    and then Scope (Callee_E) = Protected_Type_E
                  then
                     return True;
                  end if;
               end;

            end loop;

            return False;
         end Calls_Same_Target_Type;

         -------------------
         -- Is_Predefined --
         -------------------

         function Is_Predefined (Subprogram : String) return Boolean is
         begin
            return Match (Predefined, Subprogram);
         end Is_Predefined;

      --  Start of processing for Calls_Potentially_Blocking_Subprogram

      begin
         for V of Protected_Operation_Call_Graph.
           Get_Collection (Caller, Out_Neighbours)
         loop
            declare
               Callee : constant Entity_Name :=
                 Protected_Operation_Call_Graph.Get_Key (V);

               Callee_E : constant Entity_Id := Find_Entity (Callee);
               --  Entities from other compilation units have empty id
            begin
               if Is_Predefined (To_String (Callee)) then
                  --  All user-defined callers of predefined potentially
                  --  blocking subprograms have been already marked as
                  --  potentially blocking, so here we can safely assume
                  --  that any call to predefined subprogram is nonblocking.
                  null;
               else
                  if not Nonblocking_Subprograms.Contains (Callee) then
                     return True;
                  end if;
               end if;

               --  Check for external calls to a protected subprogram with
               --  the same target type as that of the protected action.
               if Callee_E = Empty
                 or else not Scope_Within_Or_Same (Scope (Callee_E),
                                                   Protected_Type_E)
               then
                  if Calls_Same_Target_Type (Callee) then
                     return True;
                  end if;
               end if;

               --  ??? remote subprograms
            end;

         end loop;

         return False;

      end Calls_Potentially_Blocking_Subprogram;

   --  Start of processing for Is_Potentially_Blocking

   begin
      return (not Nonblocking_Subprograms.Contains (EN))
        or else Calls_Potentially_Blocking_Subprogram;
   end Is_Potentially_Blocking;

   ---------------------
   -- Tasking_Objects --
   ---------------------

   function Tasking_Objects
     (Kind : Tasking_Info_Kind;
      Subp : Entity_Name)
      return Name_Sets.Set
   is
      Phase_2_Info : Name_Graphs.Map renames
        Tasking_Info_Bag (GG_Phase_2, Kind);

      C : constant Name_Graphs.Cursor := Phase_2_Info.Find (Subp);

   begin
      return (if Has_Element (C)
              then Phase_2_Info (C)
              else Name_Sets.Empty_Set);
   end Tasking_Objects;

   --------------------------------------------------------------------------
   --  Debug output routines
   --------------------------------------------------------------------------

   -----------------------------------------
   -- Print_Generated_Initializes_Aspects --
   -----------------------------------------

   procedure Print_Generated_Initializes_Aspects is
   begin
      Write_Line ("Synthesized initializes aspects:");
      for Init in Initializes_Aspects_Map.Iterate loop
         declare
            Pkg : Entity_Name      renames Initializes_Aspects_Maps.Key (Init);
            II  : Initializes_Info renames Initializes_Aspects_Map (Init);

         begin
            Indent;
            Write_Line ("Package " & To_String (Pkg)  & ":");
            Indent;
            Print_Name_Set ("LHS      : ", II.LHS);
            Print_Name_Set ("LHS_Proof: ", II.LHS_Proof);
            Print_Name_Set ("RHS      : ", II.RHS);
            Print_Name_Set ("RHS_Proof: ", II.RHS_Proof);
            Outdent;
            Outdent;
         end;
      end loop;
   end Print_Generated_Initializes_Aspects;

   ------------------------
   -- Print_Global_Graph --
   ------------------------

   procedure Print_Global_Graph (Filename : String;
                                 G        : Global_Graphs.Graph)
   is
      use Global_Graphs;

      function NDI
        (G : Graph;
         V : Vertex_Id)
         return Node_Display_Info;
      --  Pretty-printing for each vertex in the dot output

      function EDI
        (G      : Graph;
         A      : Vertex_Id;
         B      : Vertex_Id;
         Marked : Boolean;
         Colour : No_Colours)
         return Edge_Display_Info;
      --  Pretty-printing for each edge in the dot output

      ---------
      -- NDI --
      ---------

      function NDI
        (G : Graph;
         V : Vertex_Id) return Node_Display_Info
      is
         G_Id  : constant Global_Id := G.Get_Key (V);

         Shape : constant Node_Shape_T := (if G_Id.Kind = Variable
                                           then Shape_Oval
                                           else Shape_Box);

         Label : constant String :=
           (case G_Id.Kind is
              when Subprogram      => "Subprogram " & To_String (G_Id.Name),
              when Proof_Ins       => To_String (G_Id.Name) & "'Proof_Ins",
              when Inputs          => To_String (G_Id.Name) & "'Inputs",
              when Outputs         => To_String (G_Id.Name) & "'Outputs",
              when Variable        => To_String (G_Id.Name),
              when Null_Global_Id  => raise Program_Error);

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
        (G      : Graph;
         A      : Vertex_Id;
         B      : Vertex_Id;
         Marked : Boolean;
         Colour : No_Colours)
         return Edge_Display_Info
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

   --  Start of processing for Print_Global_Graph

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

   -------------------------------
   -- Print_Global_Phase_1_Info --
   -------------------------------

   procedure Print_Global_Phase_1_Info (Info : Global_Phase_1_Info) is
   begin
      Write_Line ((case Info.Kind is
                   when Kind_Subprogram                  => "Subprogram ",
                   when Kind_Entry                       => "Entry ",
                   when Kind_Task                        => "Task ",
                   when Kind_Package | Kind_Package_Body => "Package ")
        & To_String (Info.Name));

      Print_Name_Set ("Proof_Ins            :", Info.Inputs_Proof);
      Print_Name_Set ("Inputs               :", Info.Inputs);
      Print_Name_Set ("Outputs              :", Info.Outputs);
      Print_Name_Set ("Proof calls          :", Info.Proof_Calls);
      Print_Name_Set ("Definite calls       :", Info.Definite_Calls);
      Print_Name_Set ("Conditional calls    :", Info.Conditional_Calls);
      Print_Name_Set ("Local variables      :", Info.Local_Variables);

      if Info.Kind in Kind_Package | Kind_Package_Body then
         Print_Name_Set ("Local definite writes:", Info.Local_Definite_Writes);
      end if;
   end Print_Global_Phase_1_Info;

   --------------------
   -- Print_Name_Set --
   --------------------

   procedure Print_Name_Set (Header : String; Set : Name_Sets.Set) is
   begin
      Write_Line (Header);
      for Name of Set loop
         Write_Line ("   " & To_String (Name));
         --  ??? use Indent/Outdent instead of fixed amount of spaces
      end loop;
   end Print_Name_Set;

   ----------------------------
   -- Print_Tasking_Info_Bag --
   ----------------------------

   procedure Print_Tasking_Info_Bag (P : Phase) is

      Debug_Print_Tasking_Info : constant Boolean := False;
      --  Enables printing of tasking-related information

   begin
      if not Debug_Print_Tasking_Info then
         return;
      end if;

      for Kind in Tasking_Info_Kind loop
         Write_Line ("Tasking: " & Kind'Img);
         Indent;
         if not Tasking_Info_Bag (P, Kind).Is_Empty then
            for C in Tasking_Info_Bag (P, Kind).Iterate loop
               declare
                  Subp : Entity_Name   renames Key (C);
                  Objs : Name_Sets.Set renames Tasking_Info_Bag (P, Kind) (C);
               begin
                  if not Objs.Is_Empty then
                     Write_Line (To_String (Subp) & ":");
                     Indent;
                     for Obj of Objs loop
                        Write_Line (To_String (Obj));
                     end loop;
                     Outdent;
                  end if;
               end;
            end loop;
         end if;
         Outdent;
      end loop;
   end Print_Tasking_Info_Bag;

   --------------------------
   -- Register_Task_Object --
   --------------------------

   procedure Register_Task_Object
     (Type_Name : Entity_Name;
      Object    : Task_Object)
   is
      C : Task_Instances_Maps.Cursor;
      --  Cursor with a list of instances of a given task type

      Dummy : Boolean;
      --  Flag that indicates if a key was inserted or if it already existed in
      --  a map. It is required by the hashed-maps API, but not used here.

   begin
      --  Find a list of instances of the task type; if it does not exist then
      --  initialize with an empty list.
      Task_Instances.Insert (Key      => Type_Name,
                             Position => C,
                             Inserted => Dummy);

      Task_Instances (C).Append (Object);
   end Register_Task_Object;

end Flow_Generated_Globals.Phase_2;
