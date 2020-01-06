------------------------------------------------------------------------------
--                                                                          --
--                           GNAT2WHY COMPONENTS                            --
--                                                                          --
--       F L O W . G E N E R A T E D _ G L O B A L S . P H A S E _ 2        --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                Copyright (C) 2014-2020, Altran UK Limited                --
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
with Ada.Strings.Fixed;
with Ada.Strings.Unbounded;      use Ada.Strings.Unbounded;
with Ada.Text_IO;                use Ada.Text_IO;

with ALI;                        use ALI;
with Namet;                      use Namet;
with Osint;                      use Osint;
with Output;                     use Output;
with Sem_Aux;                    use Sem_Aux;
with Sem_Util;                   use Sem_Util;

with Call;                       use Call;
with Debug.Timing;               use Debug.Timing;
with Gnat2Why_Args;
with SPARK2014VSN;               use SPARK2014VSN;
with SPARK_Annotate;             use SPARK_Annotate;
with SPARK_Frame_Conditions;     use SPARK_Frame_Conditions;
with SPARK_Xrefs;                use SPARK_Xrefs;

with Common_Iterators;           use Common_Iterators;
with Flow_Refinement;            use Flow_Refinement;
with Flow_Utility;               use Flow_Utility;
with Graphs;
with Flow_Generated_Globals.Traversal; use Flow_Generated_Globals.Traversal;

with Flow_Generated_Globals.Phase_2.Traversal;
use Flow_Generated_Globals.Phase_2.Traversal;

with Flow_Generated_Globals.ALI_Serialization;
use Flow_Generated_Globals.ALI_Serialization;

with Flow_Generated_Globals.Phase_2.Read;
with Flow_Generated_Globals.Phase_2.Visibility;
use Flow_Generated_Globals.Phase_2.Visibility;

package body Flow_Generated_Globals.Phase_2 is

   GG_Generated : Boolean := False;
   --  Set to True by GG_Read once the Global Graph has been generated.

   GG_State_Constituents : Boolean := False with Ghost;
   --  Set to True by GG_Read once the mappings between abstract states and
   --  their constituents have been populated.

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

   Internal : constant Pattern_Matcher :=
     Compile ("^(ada|interfaces|system|gnat)__") with Ghost;
   pragma Unreferenced (Internal); --  ???
   --  Regexp for internal entities; for these we do not generate ALI info

   ----------------------------------------------------
   -- Constant Entity_Name for function Current_Task --
   ----------------------------------------------------

   Current_Task : constant Entity_Name :=
     To_Entity_Name (Child_Prefix & "ada__task_identification__current_task");
   --  This is used to detect calls to Ada.Task_Identification.Current_Task

   --------------------
   -- Tasking graphs --
   --------------------

   type No_Colours is (Dummy_Color);
   --  Dummy type inhabited by only a single value (similar to unit type in
   --  OCaml); used to instantiate graphs with colorless edges.

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
   --  blocking statements or calls to Current_Task from entry body or
   --  interrupt handlers.
   --
   --  Vertices correspond to subprograms and edges correspond to subprogram
   --  calls.
   --
   --  Subprogram calls are provided by the front end, i.e. they are not
   --  affected by user's annotations. Unlike Global_Graph, it contains
   --  no objects.

   Subprogram_Call_Graph : Entity_Name_Graphs.Graph :=
     Entity_Name_Graphs.Create;
   --  Call graph rooted at analyzed subprograms for detecting if a subprogram
   --  is recursive.

   Termination_Call_Graph : Entity_Name_Graphs.Graph :=
     Entity_Name_Graphs.Create;
   --  Call graph rooted at analyzed subprograms which are relevant for proving
   --  termination. This is used to determine calls to potentially nonreturning
   --  subprograms.

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

   Direct_Calls : Name_Graphs.Map;
   --  Map from names of subprograms, entries and task types to subprograms and
   --  entries that they call.
   --  ??? perhaps a map from entity names to lists (and not sets) is better,
   --  but for now let's be consistent with Flow.Slice.Compute_Globals which
   --  returns a set.

   use type Entity_Name_Graphs.Vertex_Id;

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

   package Entity_Contract_Maps is new Ada.Containers.Hashed_Maps
     (Key_Type        => Entity_Name,
      Element_Type    => Flow_Names,
      Hash            => Name_Hash,
      Equivalent_Keys => "=");

   type Global_Patch is record
      Entity   : Entity_Name;
      Contract : Flow_Names;
   end record;
   --  An updated version of a Global contract to be kept separately until a
   --  full round of resolving is done. This ensures that the algorithm uses
   --  the same intermediate contracts no matter in what order the entities
   --  are processed.

   package Global_Patch_Lists is new Ada.Containers.Doubly_Linked_Lists
     (Element_Type => Global_Patch);

   Global_Contracts : Entity_Contract_Maps.Map;

   use type Name_Sets.Set;

   use Name_Graphs;

   package Constant_Graphs is new Graphs
     (Vertex_Key   => Entity_Name,
      Key_Hash     => Name_Hash,
      Edge_Colours => No_Colours,
      Null_Key     => Entity_Name'Last,
      Test_Key     => "=");

   ----------------------------------------------------------------------
   --  Debug flags
   ----------------------------------------------------------------------

   Debug_GG_Read_Timing              : constant Boolean := False;
   --  Enables timing information for gg_read

   ----------------------------------------------------------------------
   --  State information
   ----------------------------------------------------------------------

   State_Comp_Map : Name_Graphs.Map := Name_Graphs.Empty_Map;
   --  Mapping from abstract states to their constituents, i.e.
   --  abstract_state -> {constituents}

   Comp_State_Map : Name_Maps.Map   := Name_Maps.Empty_Map;
   --  A reverse of the above mapping, i.e. constituent -> abstract_state

   State_Part_Map : Name_Graphs.Map := Name_Graphs.Empty_Map;
   --  Mapping from abstract states to their Part_Of constituents, i.e.
   --  abstract_state -> {constituents}

   Part_State_Map : Name_Maps.Map;
   --  A reverse of the above mapping, i.e. constituent -> abstract_state

   State_Abstractions : Name_Sets.Set := Name_Sets.Empty_Set;
   --  State abstractions that the GG knows of

   ----------------------------------------------------------------------
   --  Initializes information
   ----------------------------------------------------------------------

   Initialized_Vars_And_States : Name_Sets.Set;
   --  Variables and state abstractions know to be initialized

   ----------------------------------------------------------------------
   --  Ghost information
   ----------------------------------------------------------------------

   Ghost_Entities : Name_Sets.Set;
   --  Entities annotated as ghost

   ----------------------------------------------------------------------
   --  Constant information
   ----------------------------------------------------------------------

   Constants : Name_Sets.Set;
   --  Constants

   ----------------------------------------------------------------------
   --  CAE information
   ----------------------------------------------------------------------

   CAE_Entities : Name_Sets.Set;
   --  Entities annotated as Constant_After_Elaboration

   ----------------------------------------------------------------------
   --  POs information
   ----------------------------------------------------------------------

   Directly_Called_POs_In_Elaborations : Name_Sets.Set;
   --  Protected objects directly accessed in elaborations of (possibly) main
   --  subprograms.

   ----------------------------------------------------------------------
   --  Volatile information
   ----------------------------------------------------------------------

   Volatile_Vars         : Name_Sets.Set;
   Async_Writers_Vars    : Name_Sets.Set;
   Async_Readers_Vars    : Name_Sets.Set;
   Effective_Reads_Vars  : Name_Sets.Set;
   Effective_Writes_Vars : Name_Sets.Set;
   --  Volatile variables; Volatile_Vars is a union of the four other sets

   ----------------------------------------------------------------------
   --  Local subprograms
   ----------------------------------------------------------------------

   package Phase_1_Info_Maps is new Ada.Containers.Hashed_Maps
     (Key_Type        => Entity_Name,
      Element_Type    => Partial_Contract,
      Hash            => Name_Hash,
      Equivalent_Keys => "=");
   --  Container for information read from ALI files

   Phase_1_Info : Phase_1_Info_Maps.Map;
   --  Information read from ALI files

   Constant_Calls : Name_Graphs.Map;
   --  Calls from constants to subprograms in their initialization expressions
   --  ??? this should be map from Entity_Name to Name_Lists.List

   function Categorize_Calls
     (EN        : Entity_Name;
      Contracts : Entity_Contract_Maps.Map)
      return Call_Names;
   --  Equivalent of a routine with the same name from phase 1, but operating
   --  on sets of Entity_Names. Refactoring them to avoid code reuse is
   --  terribly painful, because they operate on containers with different
   --  items. Here it is intentionally undocumented; see phase 1 for comments.

   function Is_Protected_Operation (E_Name : Entity_Name) return Boolean;
   --  Return True if E_Name refers to an entry or protected subprogram

   function Is_Predefined (EN : Entity_Name) return Boolean;
   --  Returns True iff EN is a predefined entity

   procedure Register_Task_Object
     (Type_Name : Entity_Name;
      Object    : Task_Object);
   --  Register an instance Object whose type is a task type Type_Name; this
   --  will be either an explicit instance or the implicit environment task
   --  for the "main" subprogram.

   function Generated_Calls (Caller : Entity_Name) return Name_Sets.Set;
   --  Returns callees of a Caller

   function Is_Potentially_Nonreturning_Internal (EN : Entity_Name)
                                                  return Boolean;
   --  See comment for Is_Potentially_Nonreturning with Entity_Id as an input

   function Is_Recursive (EN : Entity_Name) return Boolean;
   --  Returns True iff there is an edge in the subprogram call graph that
   --  connects a subprogram to itself.

   function Mutually_Recursive (EN1, EN2 : Entity_Name) return Boolean;
   --  Returns True iff there is an edge in the subprogram call graph that
   --  connects EN1 to EN2.

   function Is_Directly_Nonreturning (EN : Entity_Name) return Boolean is
     ((Phase_1_Info.Contains (EN) and then Phase_1_Info (EN).Nonreturning)
      or else Is_Recursive (EN));
   --  Returns True iff subprogram EN does not return directly because of a
   --  non-returning statement or a (possibly indirect) recursive call.
   --
   --  It should be used only after the call graph for detecting recursive
   --  subprograms has been created and closed. ??? perhaps add Pre for this
   --
   --  Note: subprogram may still not return because of a call to non-returning
   --  subprogram.

   function Down_Project
     (Var    : Entity_Name;
      Caller : Entity_Name)
      return Name_Sets.Set;
   --  If Var is an abstract state whose refinement is visible in the body of
   --  Caller, then return the state constituents; otherwise, return a
   --  singleton set with Var itself.

   function Down_Project
     (Vars   : Name_Sets.Set;
      Caller : Entity_Name)
      return Name_Sets.Set;
   --  Same as above but lifted to sets of variables

   function Down_Project
     (G      : Global_Names;
      Caller : Entity_Name)
      return Global_Names;
   --  Same as above but lifted to sets with proof_ins, inputs and outputs
   --  ??? When down-projecting a partially visible proof_in abstract state
   --  we might get overlapping with its input/output constituents; fixit.

   procedure Up_Project (Vars      :     Name_Sets.Set;
                         Scope     :     Name_Scope;
                         Projected : out Name_Sets.Set;
                         Partial   : out Name_Sets.Set);
   --  Opposite of Down_Project: constituents from Vars that are no longer
   --  visible at Scope are converted to their encapsulating abstract states
   --  and returned in the Partial parameter; objects that remain visible are
   --  returned in Projected.

   --  ??? This routine historically belongs to Flow_Refinement, but we can't
   --  have it there and keep name visibility a private child of Phase_2.

   procedure Up_Project (Vars           :     Global_Names;
                         Projected_Vars : out Global_Names;
                         Scope          :     Name_Scope);
   --  Same as above but lifter to sets with proof_ins, inputs and outputs

   function Is_Fully_Contained (State   : Entity_Name;
                                Outputs : Name_Sets.Set;
                                Scop    : Name_Scope)
                                return Boolean;
   --  Returns True iff all constituents of State that are visible when
   --  up-projecting to Scop are among Outputs.

   function GG_Expand_Abstract_State (AS : Entity_Name) return Name_Sets.Set;
   --  Returns the constituents of AS if it is an abstract state, AS otherwise

   ----------------------------------------------------------------------
   --  Debug routines
   ----------------------------------------------------------------------

   procedure Print (G : Constant_Graphs.Graph);
   --  Print graph with dependencies between constants and their inputs

   procedure Print_Tasking_Info_Bag (P : Phase);
   --  Display the tasking-related information

   ---------------------
   -- Generated_Calls --
   ---------------------

   function Generated_Calls (Caller : Entity_Name) return Name_Sets.Set is
      C : constant Name_Graphs.Cursor := Direct_Calls.Find (Caller);
   begin
      return (if Name_Graphs.Has_Element (C)
              then Direct_Calls (C)
              else Name_Sets.Empty_Set);
   end Generated_Calls;

   function Generated_Calls (E : Entity_Id) return Node_Lists.List is
      Direct_Calls : Node_Lists.List := Node_Lists.Empty_List;
   begin
      for Callee of Generated_Calls (To_Entity_Name (E)) loop
         pragma Assert (Present (Find_Entity (Callee)));
         Direct_Calls.Append (Find_Entity (Callee));
      end loop;
      return Direct_Calls;
   end Generated_Calls;

   --------------------------
   -- GG_Is_Abstract_State --
   --------------------------

   function GG_Is_Abstract_State (EN : Entity_Name) return Boolean renames
     State_Abstractions.Contains;

   --------------------
   -- GG_Get_Globals --
   --------------------

   Null_Globals_Reported : Node_Sets.Set;
   --  Prevents repeated reports about giving null globals

   procedure GG_Get_Globals (E       : Entity_Id;
                             S       : Flow_Scope;
                             Globals : out Global_Flow_Ids)
   is
      C : constant Entity_Contract_Maps.Cursor :=
        Global_Contracts.Find (To_Entity_Name (E));

      procedure To_Flow_Id_Set (G : Global_Names);
      --  Convert to Flow_Id because down-projecting relies on visibility
      --  queries. ??? Historically, we only had visibility queries for
      --  Entity_Ids; now we also have them for Entity_Names, so we should
      --  rather down-project names and only convert results to Flow_Ids.

      --------------------
      -- To_Flow_Id_Set --
      --------------------

      procedure To_Flow_Id_Set (G : Global_Names) is
      begin
         Globals :=
           (Proof_Ins => To_Flow_Id_Set (G.Proof_Ins),
            Inputs    => To_Flow_Id_Set (G.Inputs),
            Outputs   => To_Flow_Id_Set (G.Outputs));
      end To_Flow_Id_Set;

      use type Flow_Id_Sets.Set;

   --  Start of processing for GG_Get_Globals

   begin
      if Entity_Contract_Maps.Has_Element (C) then
         To_Flow_Id_Set
           (if Ekind (E) /= E_Package
              and then Subprogram_Refinement_Is_Visible (E, S)
            then Global_Contracts (C).Refined
            else Global_Contracts (C).Proper);

         --  Down-project globals to the scope of the caller. Prevent
         --  overlapping between Proof_Ins and Inputs/Outputs, which may occur
         --  when down-projecting a partially visible Proof_In abstract state
         --  into its constituents that also happen to be Inputs or Outputs.

         Globals.Inputs    := Down_Project (Globals.Inputs,    S);
         Globals.Outputs   := Down_Project (Globals.Outputs,   S);
         Globals.Proof_Ins := Down_Project (Globals.Proof_Ins, S)
           - Globals.Inputs - Globals.Outputs;

         --  Convert to In_View/Out_View variants, as returned by Get_Globals

         Globals :=
           (Proof_Ins => Change_Variant (Globals.Proof_Ins, In_View),
            Inputs    => Change_Variant (Globals.Inputs,    In_View),
            Outputs   => Change_Variant (Globals.Outputs,   Out_View));

      else
         Globals.Proof_Ins.Clear;
         Globals.Inputs.Clear;
         Globals.Outputs.Clear;

         if XXX then
            declare
               Inserted : Boolean;
               Unused   : Node_Sets.Cursor;

            begin
               Null_Globals_Reported.Insert (New_Item => E,
                                             Position => Unused,
                                             Inserted => Inserted);

               if Inserted then
                  Ada.Text_IO.Put_Line ("Giving null globals for "
                                        & Full_Source_Name (E));
               end if;
            end;
         end if;
      end if;
   end GG_Get_Globals;

   ------------------------
   -- GG_Get_Initializes --
   ------------------------

   function GG_Get_Initializes (E : Entity_Id) return Dependency_Maps.Map is
      C : constant Entity_Contract_Maps.Cursor :=
        Global_Contracts.Find (To_Entity_Name (E));
      --  Position of the generated contract for E, if any

   begin
      if Entity_Contract_Maps.Has_Element (C) then
         declare
            Final : Flow_Names renames Global_Contracts (C);

            Inputs : constant Flow_Id_Sets.Set :=
              To_Flow_Id_Set (Final.Proper.Inputs);

            Proof_Ins : constant Flow_Id_Sets.Set :=
              To_Flow_Id_Set (Final.Proper.Proof_Ins);

            DM : Dependency_Maps.Map;

            use type Flow_Id_Sets.Set;

         begin
            if Final.Initializes.Is_Empty then
               if Inputs.Is_Empty and then Proof_Ins.Is_Empty then
                  null;
               else
                  DM.Insert
                    (Key      => Null_Flow_Id,
                     New_Item => Inputs or Proof_Ins);
               end if;
            else
               for LHS of Final.Initializes loop
                  DM.Insert
                    (Key      => Get_Flow_Id (LHS),
                     New_Item => Inputs);
               end loop;

               if not Proof_Ins.Is_Empty then
                  DM.Insert
                    (Key      => Null_Flow_Id,
                     New_Item => Proof_Ins);
               end if;
            end if;

            return DM;
         end;

      --  ??? proof asks for generated initializes on wrapper packages;
      --  to be fixed in a separate commit.

      else
         pragma Assert (Is_Wrapper_Package (E));
         return Dependency_Maps.Empty_Map;
      end if;
   end GG_Get_Initializes;

   --------------------
   -- GG_Has_Globals --
   --------------------

   function GG_Has_Globals (E : Entity_Id) return Boolean is
     (Global_Contracts.Contains (To_Entity_Name (E)));

   -------------------
   -- Is_Predefined --
   -------------------

   function Is_Predefined (EN : Entity_Name) return Boolean is
     (Match (Predefined, Strip_Child_Prefixes (To_String (EN))));

   -------------
   -- GG_Read --
   -------------

   procedure GG_Read (GNAT_Root : Node_Id) is
      Timing : Time_Token;
      --  In case we print timing information

      procedure Add_Edges;
      --  Creates edges for (conditional and unconditional) subprogram calls in
      --  the tasking-related call graphs.

      procedure Load_GG_Info_From_ALI
        (ALI_File_Name     : File_Name_Type;
         For_Current_CUnit : Boolean);
      --  Loads the GG info from an ALI file and stores them in the
      --  Subprogram_Info_List, State_Comp_Map and volatile info sets.

      procedure Note_Time (Message : String);
      --  Record timing statistics (but only in timing debug mode)

      procedure Process_Tasking_Graph;
      --  Do transitive closure of the tasking graph and put the resulting
      --  information back to bag with tasking-related information.

      ---------------
      -- Add_Edges --
      ---------------

      procedure Add_Edges is
      begin
         ----------------------------------------
         -- Create tasking-related call graphs --
         ----------------------------------------

         --  If it is a library-level subprogram with no parameters then it may
         --  be the main subprogram of a partition and thus be executed by the
         --  environment task.
         --
         --  Such a subprogram might be given either as a spec, body or
         --  instance of a generic procedure, in which case front end wraps it
         --  inside a package body. Currently GNAT does not allow subprogram
         --  renaming to be main, but this choice is implementation-specific
         --  (see AA RM 10.2(29.b)).
         --
         --  The following code mirrors front end tests in
         --  Lib.Writ.Write_ALI.Output_Main_Program_Line, but also detects
         --  main-like subprogram declaration, which we want to analyze even
         --  if there is yet no a subprogram body or it is not in SPARK.

         Detect_Main_Subprogram : declare
            U : constant Node_Id := Unit (GNAT_Root);
            S : Entity_Id;

         begin
            case Nkind (U) is
            when N_Subprogram_Body =>
               S := Unique_Defining_Entity (U);

            when N_Subprogram_Declaration =>
               S := Defining_Entity (U);

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
                  Main_Entity_Name : constant Entity_Name :=
                    To_Entity_Name (S);
               begin
                  Register_Task_Object (Type_Name => Main_Entity_Name,
                                        Object    =>
                                          (Name      => Main_Entity_Name,
                                           Instances => 1,
                                           Node      => S));
                  --  Register the main-like subprogram as a task, but use the
                  --  same entity name for type and object name.
               end;
            end if;

         end Detect_Main_Subprogram;

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
                  for Callee of Generated_Calls (Caller) loop
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

         --  To detect potentially blocking operations in protected actions,
         --  and calls to Current_Task from entry body or interrupt handlers,
         --  we create a call graph with vertices corresponding to callable
         --  entities (i.e. entries, functions and procedures).

         Add_Protected_Operation_Edges : declare
            Stack : Name_Sets.Set;
            --  We collect protected operations in SPARK and use them as seeds
            --  to grow the call graph.

            Call_Graph : Entity_Name_Graphs.Graph renames
              Protected_Operation_Call_Graph;
            --  A short alias for a long name

         begin
            --  First collect SPARK-compliant protected operations in the
            --  current compilation unit.
            for E of Entities_To_Translate loop
               if (Ekind (E) = E_Entry
                   or else (Ekind (E) in E_Function | E_Procedure
                            and then Ekind (Scope (E)) = E_Protected_Type))
                 and then Analysis_Requested (E, With_Inlined => True)
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
                  --  Add callees of the caller into the graph
                  for Callee of Generated_Calls (Caller) loop
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

                  --  Pop the caller from the stack
                  Stack.Delete (Caller);
               end;
            end loop;

            --  Close the call graph; for an empty graph it will be a no-op
            Call_Graph.Close;
         end Add_Protected_Operation_Edges;

         --  To detect if a subprogram is recursive we create a call graph
         --  where vertices correspond to subprograms and edges to subprogram
         --  calls.

         Add_Subprogram_Edges : declare
            Stack : Name_Sets.Set;
            --  We collect called subprograms and use them as seeds to grow the
            --  graph.

            Call_Graph : Entity_Name_Graphs.Graph renames
              Subprogram_Call_Graph;
            --  A short alias for a long name

         begin
            for E of Entities_To_Translate loop
               if Is_Subprogram_Or_Entry (E) then
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
                  --  Add callees of the caller into the graph
                  for Callee of Generated_Calls (Caller) loop
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

                  --  Pop the caller from the stack
                  Stack.Delete (Caller);
               end;
            end loop;

            --  Close the call graph
            Call_Graph.Close;
         end Add_Subprogram_Edges;

         Add_Termination_Edges : declare
            Stack : Name_Sets.Set;
            --  We collect called subprograms and use them as seeds to grow the
            --  graph.

            Call_Graph : Entity_Name_Graphs.Graph renames
              Termination_Call_Graph;
            --  A short alias for a long name

         begin
            for E of Entities_To_Translate loop
               if Is_Subprogram_Or_Entry (E) then
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
                  --  Add callees of the caller into the graph, but do nothing
                  --  if the caller itself is nonreturning. The caller can be
                  --  a subprogram annotated with the Terminating annotation.
                  if not Is_Directly_Nonreturning (Caller) then
                     for Callee of Generated_Calls (Caller) loop
                        --  If the Callee is predefined then it has been
                        --  already taken into account in phase 1; if it is
                        --  annotated with the Terminating annotation do not
                        --  create an edge between the caller and the callee.
                        if Is_Predefined (Callee)
                            or else
                          (Phase_1_Info.Contains (Callee)
                           and then Phase_1_Info (Callee).Has_Terminate)
                        then
                           null;

                        else
                           --  Get vertex for the callee
                           V_Callee := Call_Graph.Get_Vertex (Callee);

                           --  If there is no vertex for the callee then create
                           --  one and put the callee on the stack.
                           if V_Callee = Entity_Name_Graphs.Null_Vertex then
                              Call_Graph.Add_Vertex (Callee, V_Callee);
                              Stack.Insert (Callee);
                           end if;

                           Call_Graph.Add_Edge (V_Caller, V_Callee);
                        end if;
                     end loop;
                  end if;

                  --  Pop the caller from the stack
                  Stack.Delete (Caller);
               end;
            end loop;

            --  Close the call graph
            Call_Graph.Close;

         end Add_Termination_Edges;

         Add_Ceiling_Priority_Edges : declare
            Stack : Name_Sets.Set;
            --  We collect protected operations in SPARK and use them as seeds
            --  to grow the call graph.

            Call_Graph : Entity_Name_Graphs.Graph renames
              Ceiling_Priority_Call_Graph;
            --  A short alias for a long name

         begin
            --  First collect SPARK-compliant protected operations, task types
            --  and main-like subprograms in the current compilation unit.
            for E of Entities_To_Translate loop
               if Ekind (E) in E_Entry
                             | E_Task_Type
                             | E_Function
                             | E_Procedure
                 and then Analysis_Requested (E, With_Inlined => True)
                 and then (Is_Entry (E)
                           or else Is_Task_Type (E)
                           or else Is_Protected_Operation (E)
                           or else (Ekind (E) in E_Function | E_Procedure
                                    and then Might_Be_Main (E)))
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
                  for Callee of Generated_Calls (Caller) loop
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
      end Add_Edges;

      ---------------------------
      -- Load_GG_Info_From_ALI --
      ---------------------------

      procedure Load_GG_Info_From_ALI
        (ALI_File_Name     : File_Name_Type;
         For_Current_CUnit : Boolean)
      is
         pragma Unreferenced (For_Current_CUnit);

         ALI_File_Name_Str : constant String :=
           Get_Name_String (Full_Lib_File_Name (ALI_File_Name));

         ALI_File : Ada.Text_IO.File_Type;

         type GG_Parsing_Status is (Before, Started, Finished);

         GG_Parsing_State : GG_Parsing_Status := Before;
         Found_Version    : Boolean := False;
         --  This will be set to True once we find the end marker

         procedure Corrupted_ALI_File (Msg : String)
         with No_Return;
         --  Issues an error about the ALI file being corrupted and suggests
         --  the usage of "gnatprove --clean".

         procedure Parse_GG_Line (Line : String) with
           Pre => Line'Length >= 3 and then
                  Line (Line'First .. Line'First + 2) = "GG ";
         --  Parse single line of the GG section

         ------------------------
         -- Corrupted_ALI_File --
         ------------------------

         procedure Corrupted_ALI_File (Msg : String) is
         begin
            Close (ALI_File);
            Abort_With_Message
              ("Corrupted ali file detected (" & ALI_File_Name_Str & "): " &
                 Msg &
                 ". Call gnatprove with ""--clean"".");
         end Corrupted_ALI_File;

         -------------------
         -- Parse_GG_Line --
         -------------------

         procedure Parse_GG_Line (Line : String) is

            use Flow_Generated_Globals.Phase_2.Read;

            procedure Serialize is new Serialize_Discrete (ALI_Entry_Kind);

            procedure Serialize (V : out Partial_Contract);

            ---------------
            -- Serialize --
            ---------------

            procedure Serialize (V : out Partial_Contract) is

               procedure Serialize is new Serialize_Discrete (Entity_Kind);
               procedure Serialize is new Serialize_Discrete (Boolean);
               procedure Serialize is new Serialize_Discrete
                 (Globals_Origin_T);

               procedure Serialize (G : out Global_Names; Label : String);
               procedure Serialize (V : out Name_Tasking_Info);

               ---------------
               -- Serialize --
               ---------------

               procedure Serialize (G : out Global_Names; Label : String) is
               begin
                  Serialize (G.Proof_Ins, Label & "proof_in");
                  Serialize (G.Inputs,    Label & "input");
                  Serialize (G.Outputs,   Label & "output");
               end Serialize;

               procedure Serialize (V : out Name_Tasking_Info) is
               begin
                  for Kind in Tasking_Info_Kind loop
                     Serialize (V (Kind), Kind'Img);
                  end loop;
               end Serialize;

            --  Start of processing for Serialize

            begin
               Serialize (V.Local, "local");
               Serialize (V.Kind);
               if V.Kind in E_Function | E_Procedure then
                  Serialize (V.Is_Protected);
               else
                  --  Dummy value to ensure that the OUT parameter is written
                  V.Is_Protected := False;
               end if;
               if V.Kind = E_Package then
                  Serialize (V.Is_Library_Level);
               else
                  --  Dummy value to ensure that the OUT parameter is written
                  V.Is_Library_Level := False;
               end if;
               Serialize (V.Origin);
               Serialize (V.Parents);
               Serialize (V.Globals.Proper,  "proper_");
               Serialize (V.Globals.Refined, "refined_");
               if V.Kind = E_Package then
                  Serialize (V.Globals.Initializes, "initializes");
               end if;
               Serialize (V.Globals.Calls.Proof_Calls,
                          "calls_proof");
               Serialize (V.Globals.Calls.Definite_Calls,
                          "calls");
               Serialize (V.Globals.Calls.Conditional_Calls,
                          "calls_conditional");

               if V.Kind = E_Package then
                  Serialize (V.Local_Variables, "local_var");
               end if;

               if V.Kind in Entry_Kind
                          | E_Function
                          | E_Procedure
                          | E_Task_Type
                          | E_Package
               then
                  --  ??? use Is_Proper_Callee here
                  if V.Kind /= E_Task_Type then
                     Serialize (V.Has_Terminate);
                     Serialize (V.Nonreturning);
                     Serialize (V.Nonblocking);
                  end if;
                  Serialize (V.Tasking);
               end if;
            end Serialize;

            procedure Clear (G : in out Flow_Names);
            pragma Unreferenced (Clear);

            -----------
            -- Clear --
            -----------

            procedure Clear (G : in out Flow_Names) is
            begin
               G.Proper.Proof_Ins.Clear;
               G.Proper.Inputs.Clear;
               G.Proper.Outputs.Clear;

               G.Refined.Proof_Ins.Clear;
               G.Refined.Inputs.Clear;
               G.Refined.Outputs.Clear;

               G.Initializes.Clear;

               G.Calls.Proof_Calls.Clear;
               G.Calls.Conditional_Calls.Clear;
               G.Calls.Definite_Calls.Clear;
            end Clear;

            --  Local variables

            K : ALI_Entry_Kind;

         --  Parse_GG_Line

         begin
            New_GG_Line (Line);
            Serialize (K);
            case K is
               when EK_End_Marker =>
                  if GG_Parsing_State = Started then
                     GG_Parsing_State := Finished;
                  else
                     Corrupted_ALI_File ("unexpected GG end marker");
                  end if;

               when EK_State_Map =>
                  declare
                     State : Entity_Name;

                     State_Pos : Name_Graphs.Cursor;
                     Inserted  : Boolean;

                  begin
                     Serialize (State);
                     State_Comp_Map.Insert (Key      => State,
                                            Position => State_Pos,
                                            Inserted => Inserted);
                     pragma Assert (Inserted);

                     Serialize (State_Comp_Map (State_Pos));

                     for Constituent of State_Comp_Map (State_Pos) loop
                        Comp_State_Map.Insert (Constituent, State);
                     end loop;

                     State_Abstractions.Include (State);
                  end;

               when EK_Part_Of =>
                  declare
                     State   : Entity_Name;
                     Part_Of : Entity_Name;

                     State_Pos : Name_Graphs.Cursor;
                     Part_Pos  : Name_Maps.Cursor;
                     Inserted  : Boolean;

                  begin
                     Serialize (State);
                     Serialize (Part_Of);

                     State_Part_Map.Insert (Key      => State,
                                            Position => State_Pos,
                                            Inserted => Inserted);

                     State_Part_Map (State_Pos).Include (Part_Of);

                     Part_State_Map.Insert (Key      => Part_Of,
                                            New_Item => State,
                                            Position => Part_Pos,
                                            Inserted => Inserted);

                     pragma Assert
                       (Inserted
                          or else
                        Part_State_Map (Part_Pos) = State);

                     State_Abstractions.Include (State);
                  end;

               when EK_Remote_States =>
                  Serialize (State_Abstractions);

               when EK_Predef_Init_Entities =>
                  Serialize (Initialized_Vars_And_States);

               when EK_Ghost_Entities =>
                  Serialize (Ghost_Entities);

               when EK_CAE_Entities =>
                  Serialize (CAE_Entities);

               when EK_Constants =>
                  Serialize (Constants);

               when EK_Volatiles =>
                  Serialize (Async_Readers_Vars,    "AR");
                  Serialize (Async_Writers_Vars,    "AW");
                  Serialize (Effective_Reads_Vars,  "ER");
                  Serialize (Effective_Writes_Vars, "EW");

               when EK_Globals =>
                  --  ??? this line should be loaded only when
                  --  For_Current_Unit or else not V.The_Global_Info.Local
                  declare
                     Entity : Entity_Name;

                     Pos      : Phase_1_Info_Maps.Cursor;
                     Inserted : Boolean;

                  begin
                     Serialize (Entity);

                     --  Move global information to separate container
                     Phase_1_Info.Insert
                       (Key      => Entity,
                        Position => Pos,
                        Inserted => Inserted);

                     pragma Assert (Inserted);

                     Serialize (Phase_1_Info (Pos));

                     Global_Contracts.Insert
                       (Key      => Entity,
                        New_Item => Phase_1_Info (Pos).Globals);

                     --  ??? Clear the original map as a sanity check
                     --  Clear (Phase_1_Info (Entity_Pos).Globals);

                     for Kind in Tasking_Info_Kind loop
                        if not Phase_1_Info (Pos).Tasking (Kind).Is_Empty then
                           Tasking_Info_Bag (GG_Phase_1, Kind).Insert
                             (Entity,
                              Phase_1_Info (Pos).Tasking (Kind));
                        end if;
                     end loop;

                     if Present (Root_Entity)
                       and then Is_Subprogram (Root_Entity)
                       and then Might_Be_Main (Root_Entity)
                       and then Phase_1_Info (Pos).Kind = E_Package
                       and then Phase_1_Info (Pos).Is_Library_Level
                     then
                        Directly_Called_POs_In_Elaborations.Union
                          (Phase_1_Info (Pos).Tasking (Locks));
                     end if;

                     Register_Nested_Scopes
                       (Entity, Phase_1_Info (Pos).Parents);
                  end;

               when EK_Constant_Calls =>
                  declare
                     Const_Pos : Name_Graphs.Cursor;
                     --  Position of the caller in the direct calls graph

                     Inserted : Boolean;

                     Const : Entity_Name;

                  begin
                     Serialize (Const);
                     Constant_Calls.Insert (Key      => Const,
                                            Position => Const_Pos,
                                            Inserted => Inserted);

                     pragma Assert (Inserted);

                     Serialize (Constant_Calls (Const_Pos));
                  end;

               when EK_Protected_Instance =>
                  declare
                     Variable   : Entity_Name;
                     Prio_Kind  : Priority_Kind;
                     Prio_Value : Int;

                     procedure Serialize is new
                       Flow_Generated_Globals.Phase_2.Read.Serialize_Discrete
                         (Priority_Kind);

                     C : Entity_Name_To_Priorities_Maps.Cursor;
                     --  Position of a list of protected components of a global
                     --  variable and their priorities.

                     Dummy : Boolean;
                     --  Flag that indicates if a key was inserted or if
                     --  it already existed in a map. It is required by the
                     --  hashed-maps API, but not used here.

                  begin
                     Serialize (Variable);
                     Serialize (Prio_Kind);
                     if Prio_Kind = Static then
                        Serialize (Prio_Value);
                     else
                        Prio_Value := 0;
                     end if;

                     --  Find a list of protected components of a global
                     --  variable; if it does not exist then initialize with
                     --  an empty list.

                     Protected_Objects.Insert
                       (Key      => Variable,
                        Position => C,
                        Inserted => Dummy);

                     Protected_Objects (C).Append
                       (Priority_Value'(Kind  => Prio_Kind,
                                        Value => Prio_Value));
                  end;

               when EK_Task_Instance =>
                  declare
                     Typ       : Entity_Name;
                     Object    : Entity_Name;
                     Instances : Instance_Number;

                  begin
                     Serialize (Typ);
                     Serialize (Object);
                     Serialize (Instances);

                     Register_Task_Object
                       (Typ,
                        Task_Object'(Name      => Object,
                                     Instances => Instances,
                                     Node      => Find_Entity (Object)));
                  end;

               when EK_Max_Queue_Length =>
                  declare
                     Entry_Name       : Entity_Name;
                     Max_Queue_Length : Nat;

                  begin
                     Serialize (Entry_Name);
                     Serialize (Max_Queue_Length);

                     --  As we are registering the Max_Queue_Lenght for every
                     --  reference, this might appear in more than one ALI file
                     --  and therefore we use Include.

                     Max_Queue_Lengths.Include
                       (Key      => Entry_Name,
                        New_Item => Max_Queue_Length);
                  end;

               when EK_Direct_Calls =>
                  declare
                     Caller : Entity_Name;

                     Caller_Pos : Name_Graphs.Cursor;
                     --  Position of the caller in the direct calls graph

                     Inserted : Boolean;

                  begin
                     Serialize (Caller);

                     Direct_Calls.Insert (Key      => Caller,
                                          Position => Caller_Pos,
                                          Inserted => Inserted);

                     --  ??? this should be asserted and should never crash
                     if not Inserted then
                        raise Program_Error with "name clash";
                     end if;

                     Serialize (Direct_Calls (Caller_Pos));
                  end;

               when EK_Flow_Scope =>
                  declare
                     Entity : Entity_Name;
                     Info   : Name_Info_T;

                     Present : Boolean;

                     procedure Serialize is new
                       Flow_Generated_Globals.Phase_2.Read.Serialize_Discrete
                         (Boolean);

                     procedure Serialize is new
                       Flow_Generated_Globals.Phase_2.Read.Serialize_Discrete
                         (Declarative_Part);

                  begin
                     Serialize (Entity);
                     Serialize (Info.Is_Package);
                     Serialize (Info.Is_Private);

                     Serialize (Present);
                     if Present then
                        Serialize (Info.Instance_Parent);
                     else
                        Info.Instance_Parent := Null_Entity_Name;
                     end if;

                     Serialize (Present);
                     if Present then
                        Serialize (Info.Template);
                     else
                        Info.Template := Null_Entity_Name;
                     end if;

                     Serialize (Present);
                     if Present then
                        Serialize (Info.Container.Ent);
                        Serialize (Info.Container.Part);
                        Info.Parent := Null_Entity_Name;
                     else
                        Info.Container := (Null_Entity_Name, Null_Part);
                        Serialize (Info.Parent);
                     end if;

                     Register_Name_Scope (Entity, Info);
                  end;

            end case;

            Terminate_GG_Line;
         end Parse_GG_Line;

      --  Start of processing for Load_GG_Info_From_ALI

      begin
         Open (ALI_File, In_File, ALI_File_Name_Str);

         while not End_Of_File (ALI_File) loop
            declare
               Line : constant String := Get_Line (ALI_File);

            begin
               if Line'Length >= 3 then
                  declare
                     Header : String renames Line (1 .. 3);

                  begin
                     if Header = "QQ " then
                        Found_Version := Line = "QQ SPARKVERSION " &
                          SPARK2014_Static_Version_String;

                     elsif Header = "GG " then
                        if Found_Version then
                           case GG_Parsing_State is
                              when Before | Started =>
                                 GG_Parsing_State := Started;
                                 Parse_GG_Line (Line);

                              when Finished =>
                                 Corrupted_ALI_File
                                   ("GG data after GG end marker");

                           end case;

                        else
                           Corrupted_ALI_File ("inconsistent spark version");
                        end if;
                     end if;
                  end;
               end if;
            end;
         end loop;

         if GG_Parsing_State = Started then
            --  If we started but not finished then the file is corrupted
            Corrupted_ALI_File ("missing end marker");
         end if;

         Close (ALI_File);
      end Load_GG_Info_From_ALI;

      ---------------
      -- Note_Time --
      ---------------

      procedure Note_Time (Message : String) is
      begin
         if Debug_GG_Read_Timing then
            Timing_Phase_Completed (Timing, Message);
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
                        --  Flag that indicates if a key was inserted or if it
                        --  already existed in a map. It is required by the
                        --  hashed-maps API, but not used here.

                     begin
                        --  Only do something if S accesses any objects
                        if Name_Graphs.Has_Element (S_C) then
                           Tasking_Info_Bag (GG_Phase_2, Kind).Insert
                             (Key      => TN,
                              Position => T_C,
                              Inserted => Inserted);

                           for Var of Phase_1_Info (S_C) loop
                              Tasking_Info_Bag (GG_Phase_2, Kind) (T_C).
                                Union (GG_Expand_Abstract_State (Var));
                           end loop;
                        end if;
                     end;
                  end loop;
               end Collect_From;

            begin
               --  Now graph G is a transitive (but not reflexive!) closure. We
               --  need to explicitly collect objects accessed by the task
               --  itself, and then all subprogram called it calls (directly or
               --  indirectly).

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

   --  Start of processing for GG_Read

   begin
      Current_Mode := GG_Read_Mode;

      Timing_Start (Timing);

      --  Load information from all ALI files
      for Index in ALIs.First .. ALIs.Last loop
         Load_GG_Info_From_ALI
           (ALI_File_Name     => ALIs.Table (Index).Afile,
            For_Current_CUnit => Index = ALIs.First);
      end loop;

      Flow_Generated_Globals.Phase_2.Traversal.Dump_Tree;

      Flow_Generated_Globals.Phase_2.Visibility.Connect_Name_Scopes;

      Volatile_Vars.Union (Async_Readers_Vars);
      Volatile_Vars.Union (Async_Writers_Vars);
      Volatile_Vars.Union (Effective_Reads_Vars);
      Volatile_Vars.Union (Effective_Writes_Vars);

      GG_State_Constituents := True;

      Note_Time ("gg_read - ALI files read");

      Add_Edges;

      Note_Time ("gg_read - edges added");

      Resolve_Globals : declare

         use type Ada.Containers.Count_Type;

         procedure Debug (Msg : String);
         pragma Unreferenced (Debug);

         procedure Debug (Label : String; E : Entity_Name);
         --  Display Label followed by the entity name of E

         procedure Dump_Contract (Scop : Entity_Id);
         procedure Dump_Main_Unit_Contracts (Highlight : Entity_Name);
         --  Debug utilities

         procedure Filter_Local
           (E : Entity_Name; Names : in out Name_Sets.Set)
         with Post => Names.Is_Subset (Names'Old);

         procedure Fold (Folded    :        Entity_Name;
                         Analyzed  :        Entity_Name;
                         Contracts :        Entity_Contract_Maps.Map;
                         Patches   : in out Global_Patch_Lists.List)
         with Post => Patches.Length >= Patches.Length'Old;
         --  Resolve globals of Folded and append the update to Patches

         procedure Do_Global (Analyzed  :        Entity_Name;
                              Contracts : in out Entity_Contract_Maps.Map);
         --  Recursively resolve globals of Folded and entities nested in it;
         --  update Contracts.

         procedure Resolve_Constants
           (Contracts      :     Entity_Contract_Maps.Map;
            Constant_Graph : out Constant_Graphs.Graph);
         --  Create graph with dependencies between constants and their inputs

         function Resolved_To_Variable_Input
           (E              : Entity_Name;
            Constant_Graph : Constant_Graphs.Graph)
            return Boolean
           with Pre => Constant_Calls.Contains (E);
         --  Returns True iff the initialization expression of E is resolved as
         --  dependend on a variable input.

         procedure Strip_Constants
           (From           : in out Flow_Names;
            Constant_Graph :        Constant_Graphs.Graph);
         --  Filter constants without variable from contract

         Highlighted : Any_Entity_Name := Null_Entity_Name;

         Indent : constant String := "  ";
         --  Indentation for debug output

         -----------
         -- Debug --
         -----------

         procedure Debug (Msg : String) is
         begin
            if XXX then
               Ada.Text_IO.Put_Line (Msg);
            end if;
         end Debug;

         procedure Debug (Label : String; E : Entity_Name) is
         begin
            if XXX then
               Ada.Text_IO.Put_Line (Label & " " & To_String (E));
            end if;
         end Debug;

         -------------------
         -- Dump_Contract --
         -------------------

         procedure Dump_Contract (Scop : Entity_Id) is
            C : constant Entity_Contract_Maps.Cursor :=
              Global_Contracts.Find (To_Entity_Name (Scop));

            procedure Dump (Label : String; Vars : Name_Sets.Set);

            procedure Dump (Label : String; G : Global_Names);
            --  Dump globals, if any

            procedure Dump (Calls : Call_Names);
            --  Dump calls, if any

            ----------
            -- Dump --
            ----------

            procedure Dump (Label : String; Vars : Name_Sets.Set) is
            begin
               if not Vars.Is_Empty then
                  Ada.Text_IO.Put (Indent & Indent & Indent & Label & ":");
                  for Var of Vars loop
                     Ada.Text_IO.Put (" ");
                     if Var = Highlighted then
                        Term_Info.Set_Style (Bright);
                     end if;

                     if Is_Heap_Variable (Var) then
                        Ada.Text_IO.Put (Name_Of_Heap_Variable);
                     else
                        declare
                           E : constant Entity_Id := Find_Entity (Var);

                        begin
                           Ada.Text_IO.Put
                             (if Present (E)
                              then Full_Source_Name (E)
                              else To_String (Var));
                        end;
                     end if;

                     if Var = Highlighted then
                        Term_Info.Set_Style (Normal);
                     end if;
                  end loop;
                  Ada.Text_IO.New_Line;
               end if;
            end Dump;

            procedure Dump (Calls : Call_Names) is
            begin
               if not Calls.Proof_Calls.Is_Empty
                 or else not Calls.Conditional_Calls.Is_Empty
                 or else not Calls.Definite_Calls.Is_Empty
               then
                  Ada.Text_IO.Put_Line (Indent & Indent & "Calls  =>");
                  Dump ("Proof      ", Calls.Proof_Calls);
                  Dump ("Conditional", Calls.Conditional_Calls);
                  Dump ("Definite   ", Calls.Definite_Calls);
               end if;
            end Dump;

            procedure Dump (Label : String; G : Global_Names) is
            begin
               if not G.Proof_Ins.Is_Empty
                 or else not G.Inputs.Is_Empty
                 or else not G.Outputs.Is_Empty
               then
                  Ada.Text_IO.Put_Line (Indent & Indent & Label & " =>");
                  Dump ("Proof_Ins  ", G.Proof_Ins);
                  Dump ("Inputs     ", G.Inputs);
                  Dump ("Outputs    ", G.Outputs);
               end if;
            end Dump;

         --  Start of processing for Dump_Entity_Contract

         begin
            --  ??? For protected types we don't record ALI info now
            if Ekind (Scop) /= E_Protected_Type then
               declare
                  Contr : Flow_Names renames Global_Contracts (C);

                  Scop_Name : constant Entity_Name := To_Entity_Name (Scop);

                  use Ada.Strings;

               begin
                  if Scop_Name = Highlighted then
                     Term_Info.Set_Style (Bright);
                  end if;

                  Ada.Text_IO.Put_Line
                    (Indent &
                     Ekind (Scop)'Image & ": " &
                     Full_Source_Name (Scop) &
                     " (" &
                     Ada.Strings.Fixed.Trim
                       (Source => Entity_Name'Image (Scop_Name),
                        Side   => Left) &
                     ")");

                  if Scop_Name = Highlighted then
                     Term_Info.Set_Style (Normal);
                  end if;

                  Dump ("Global",         Contr.Proper);
                  Dump ("Refined_Global", Contr.Refined);
                  Dump (Contr.Calls);

                  case Ekind (Scop) is
                     when E_Function | E_Procedure =>
                        --  Ada.Text_IO.Put_Line
                        --    (Indent & Indent & "Nonblocking  : " &
                        --    Boolean'Image (Contr.Nonblocking));
                        null;

                     when E_Package =>
                        --  ??? by reusing the Dump procedure defined for
                        --  Input/Ouput/Proof_In, we get an extra indentation
                        Dump ("Initializes  ", Contr.Initializes);

                     when others =>
                        null;
                  end case;
--
--                    for Kind in Tasking_Info_Kind loop
--                       if not Contr.Tasking (Kind).Is_Empty then
--                          Dump (Kind'Img, Contr.Tasking (Kind));
--                       end if;
--                    end loop;
                  --  Ada.Text_IO.New_Line;
               end;
            end if;
         end Dump_Contract;

         ------------------------------
         -- Dump_Main_Unit_Contracts --
         ------------------------------

         procedure Dump_Main_Unit_Contracts (Highlight : Entity_Name) is
         begin
            if Debug_Partial_Contracts then
               Highlighted := Highlight;
               Iterate_Main_Unit (Dump_Contract'Access);
               Highlighted := Null_Entity_Name;
               Ada.Text_IO.New_Line;
            end if;
         end Dump_Main_Unit_Contracts;

         ------------------
         -- Filter_Local --
         ------------------

         procedure Filter_Local
           (E : Entity_Name; Names : in out Name_Sets.Set)
         is
            Remote : Name_Sets.Set;
         begin
            for N of Names loop
               if Is_Heap_Variable (N)
                 or else not Scope_Within_Or_Same (N, E)
               then
                  Remote.Insert (N);
               end if;
            end loop;

            Name_Sets.Move (Target => Names,
                            Source => Remote);
         end Filter_Local;

         ----------
         -- Fold --
         ----------

         procedure Fold (Folded    :        Entity_Name;
                         Analyzed  :        Entity_Name;
                         Contracts :        Entity_Contract_Maps.Map;
                         Patches   : in out Global_Patch_Lists.List)
         is
            Original : Flow_Names;
            --  In phase 1 this is a renaming, so we don't create a copy. In
            --  phase 2 we cannot have a renaming, because we might be folding
            --  parents that have not been processed in phase 1, e.g. we might
            --  be analysing a System.Something unit provided by GNAT without
            --  analysing its parent System unit.

            function Callee_Globals
              (Callee : Entity_Name;
               Caller : Entity_Name)
               return Global_Names;

            function Collect (Caller : Entity_Name) return Flow_Names
            with Post => Is_Empty (Collect'Result.Proper);

            function Is_Empty (Globals : Global_Names) return Boolean is
              (Globals.Proof_Ins.Is_Empty
                 and then Globals.Inputs.Is_Empty
                 and then Globals.Outputs.Is_Empty)
              with Ghost;
            --  Returns True iff the Globals contract is empty

            --------------------
            -- Callee_Globals --
            --------------------

            function Callee_Globals
              (Callee : Entity_Name;
               Caller : Entity_Name)
               return Global_Names
            is
               C : constant Entity_Contract_Maps.Cursor :=
                 Contracts.Find (Callee);

            begin
               if Entity_Contract_Maps.Has_Element (C)
                 and then Scope_Within_Or_Same
                   (Inner => Callee, Outer => Analyzed)
               then
                  return Down_Project (Contracts (C).Proper, Caller);
               else
                  --  Debug ("Ignoring call to", E);
                  return Global_Names'(others => <>);
               end if;
            end Callee_Globals;

            -------------
            -- Collect --
            -------------

            function Collect (Caller : Entity_Name) return Flow_Names is
               Result_Proof_Ins : Name_Sets.Set := Original.Refined.Proof_Ins;
               Result_Inputs    : Name_Sets.Set := Original.Refined.Inputs;
               Result_Outputs   : Name_Sets.Set := Original.Refined.Outputs;
               --  ??? by keeping these separate we don't have to care about
               --  maintaing the Global_Nodes invariant.

               Result : Flow_Names;

            begin
               Result.Calls := Categorize_Calls (Caller, Contracts);

               --  Now collect their globals

               for Callee of Result.Calls.Definite_Calls loop
                  declare
                     G : constant Global_Names :=
                       Callee_Globals (Callee => Callee, Caller => Folded);

                  begin
                     Result_Proof_Ins.Union (G.Proof_Ins);
                     Result_Inputs.Union (G.Inputs);
                     Result_Outputs.Union (G.Outputs);
                  end;
               end loop;

               for Callee of Result.Calls.Proof_Calls loop
                  declare
                     G : constant Global_Names :=
                       Callee_Globals (Callee => Callee, Caller => Folded);

                  begin
                     Result_Proof_Ins.Union (G.Proof_Ins);
                     Result_Proof_Ins.Union (G.Inputs);
                     Result_Outputs.Union (G.Outputs);
                  end;
               end loop;

               --  For conditional calls do as above, but also connect the
               --  caller's Inputs vertices to the callee's Outputs vertices.
               --  This models code like:
               --
               --     if Condition then
               --        Output := ...;
               --     end if;
               --
               --  as:
               --
               --     if Condition then
               --        Output := ...;
               --     else
               --        Output := Output;  <<< artificial read of Output
               --     end if;
               --
               --  which adds an dummy assignment.

               for Callee of Result.Calls.Conditional_Calls loop
                  declare
                     G : constant Global_Names :=
                       Callee_Globals (Callee => Callee, Caller => Folded);
                  begin
                     Result_Proof_Ins.Union (G.Proof_Ins);
                     Result_Inputs.Union (G.Inputs);
                     Result_Inputs.Union (G.Outputs);
                     Result_Outputs.Union (G.Outputs);
                  end;
               end loop;

               --  Post-processing
               Result_Proof_Ins.Difference (Result_Inputs);

               declare
                  Proof_Ins_Outs : constant Name_Sets.Set :=
                    Result_Proof_Ins and Result_Outputs;
               begin
                  Result_Proof_Ins.Difference (Proof_Ins_Outs);
                  Result_Inputs.Union (Proof_Ins_Outs);
               end;

               Result.Refined :=
                 (Proof_Ins => Result_Proof_Ins,
                  Inputs    => Result_Inputs,
                  Outputs   => Result_Outputs);

               return Result;
            end Collect;

            --  Local variables

            Update : Flow_Names;

         --  Start of processing for Fold

         begin
            Debug ("Folding", Folded);

            --  See comment above that explains why Original is not a renaming
            if Contracts.Contains (Folded) then
               Original := Contracts (Folded);
            else
               goto Fold_Children;
            end if;

            --  First we resolve globals coming from the callees...
            Update := Collect (Folded);

            --  ... and then up-project them as necessary

            Up_Project (Update.Refined, Update.Proper,
                        (Ent => Folded, Part => Visible_Part));

            pragma Assert (Phase_1_Info.Contains (Folded));

            --  Handle package Initializes aspect
            if Phase_1_Info (Folded).Kind = E_Package then
               declare
                  P : Partial_Contract renames Phase_1_Info (Folded);

                  True_Outputs : constant Name_Sets.Set :=
                    (Update.Proper.Outputs - Update.Proper.Inputs) or
                    Original.Initializes;

               begin
                  Update.Initializes := True_Outputs and P.Local_Variables;

                  Initialized_Vars_And_States.Union (Update.Initializes);

                  --  We needed reads of the local variables in the package
                  --  elaboration to know which of the writes are pure outputs.
                  --  Now we remove those reads and what remains is the RHS of
                  --  the generated Initializes contract. Similarly, we filter
                  --  local variables from the implicit "Proof_Ins".

                  Update.Proper.Inputs.Difference (P.Local_Variables);
                  Update.Proper.Proof_Ins.Difference (P.Local_Variables);
               end;
            end if;

            Filter_Local (Analyzed, Update.Calls.Proof_Calls);
            Filter_Local (Analyzed, Update.Calls.Definite_Calls);
            Filter_Local (Analyzed, Update.Calls.Conditional_Calls);

            Patches.Append
              (Global_Patch'(Entity   => Folded,
                             Contract => Update));

            <<Fold_Children>>

            for Child of Traversal.Scope_Map (Folded) loop
               Fold (Child, Analyzed, Contracts, Patches);
            end loop;
         end Fold;

         ---------------
         -- Do_Global --
         ---------------

         procedure Do_Global (Analyzed  :        Entity_Name;
                              Contracts : in out Entity_Contract_Maps.Map)
         is
         begin
            Debug ("Do_Global", Analyzed);

            for Child of Traversal.Scope_Map (Analyzed) loop
               Do_Global (Child, Contracts);
            end loop;

            if Analyzed = Standard_Standard
              or else not Is_Leaf (Analyzed)
            then
               declare
                  Patches : Global_Patch_Lists.List;
               begin
                  Fold (Folded    => Analyzed,
                        Analyzed  => Analyzed,
                        Contracts => Contracts,
                        Patches   => Patches);

                  for Patch of Patches loop
                     Contracts (Patch.Entity) := Patch.Contract;
                  end loop;
               end;
            end if;
         end Do_Global;

         -----------------------
         -- Resolve_Constants --
         -----------------------

         procedure Resolve_Constants
           (Contracts      :     Entity_Contract_Maps.Map;
            Constant_Graph : out Constant_Graphs.Graph)
         is
            Todo : Name_Sets.Set;
            --  Names to be processed (either constants or subprograms called
            --  (directly or indirectly) in their initialization expressions.

            function To_List (E : Entity_Name) return Name_Lists.List
            with Post => To_List'Result.Length = 1
                           and then
                         To_List'Result.First_Element = E;
            --  Returns a singleton list with E

            -------------
            -- To_List --
            -------------

            function To_List (E : Entity_Name) return Name_Lists.List is
               Singleton : Name_Lists.List;
            begin
               Singleton.Append (E);
               return Singleton;
            end To_List;

            Variable : constant Name_Lists.List := To_List (Variable_Input);
            --  A singleton container with a special value that represents
            --  a dependency on a variable input. (By having a special-value
            --  with the same type as non-variable dependencies we avoid
            --  discriminated records, which would be very verbose.)

            -------------------------------------------------------------------
            --  List utilities
            -------------------------------------------------------------------

            procedure Append
              (List : in out Name_Lists.List;
               Set  :        Name_Sets.Set)
            with Post => List.Length = List.Length'Old + Set.Length;

            function Direct_Inputs_Of_Constant
              (E : Entity_Name)
               return Name_Lists.List;
            --  Returns variable inputs of the initialization of constant E

            function Direct_Inputs_Of_Subprogram
              (E : Entity_Name)
               return Name_Lists.List
            with Pre => Contracts.Contains (E);
            --  Returns variable inputs coming from the globals or calls of
            --  subprogram E.

            function Pick_Constants (From : Name_Sets.Set) return Name_Sets.Set
              with Post => Pick_Constants'Result.Is_Subset (Of_Set => From)
                             and then
                           (for all E of Pick_Constants'Result =>
                               Constant_Calls.Contains (E));
            --  Returns constants contained in the given set

            procedure Seed (Constants : Name_Sets.Set);
            --  Seeds the Constant_Graph and Todo with given Constants

            -------------------------------------------------------------------
            --  Bodies
            -------------------------------------------------------------------

            ------------
            -- Append --
            ------------

            procedure Append
              (List : in out Name_Lists.List;
               Set  :        Name_Sets.Set)
            is
            begin
               for E of Set loop
                  List.Append (E);
               end loop;
            end Append;

            -------------------------------
            -- Direct_Inputs_Of_Constant --
            -------------------------------

            function Direct_Inputs_Of_Constant
              (E : Entity_Name)
               return Name_Lists.List
            is
               S : Name_Sets.Set renames Constant_Calls (E);
               L : Name_Lists.List;
               --  ??? this conversion is ugly, do something about it
            begin
               for Call of S loop
                  L.Append (Call);
               end loop;

               return L;
            end Direct_Inputs_Of_Constant;

            ---------------------------------
            -- Direct_Inputs_Of_Subprogram --
            ---------------------------------

            function Direct_Inputs_Of_Subprogram
              (E : Entity_Name)
               return Name_Lists.List
            is
               Globals : Flow_Names renames Contracts (E);

               function Has_Variables (G : Name_Sets.Set) return Boolean is
                 (for some C of G => not Constant_Calls.Contains (C));

               Inputs : Name_Lists.List;

            begin
               if Has_Variables (Globals.Refined.Proof_Ins)
                 or else Has_Variables (Globals.Refined.Inputs)
               then
                  return Variable;
               else
                  Append (Inputs, Pick_Constants (Globals.Refined.Inputs));
                  Append (Inputs, Globals.Calls.Conditional_Calls);
                  Append (Inputs, Globals.Calls.Definite_Calls);

                  --  ??? calls to Pick_Constants repeat iterations done by
                  --  Has_Variables, but they stay within the same complexity
                  --  class and makes the code shorter.

                  return Inputs;
               end if;
            end Direct_Inputs_Of_Subprogram;

            --------------------
            -- Pick_Constants --
            --------------------

            function Pick_Constants
              (From : Name_Sets.Set)
               return Name_Sets.Set
            is
               Constants : Name_Sets.Set;
            begin
               for E of From loop
                  if Constant_Calls.Contains (E) then
                     Constants.Insert (E);
                  end if;
               end loop;

               return Constants;
            end Pick_Constants;

            ----------
            -- Seed --
            ----------

            procedure Seed (Constants : Name_Sets.Set) is
            begin
               for E of Constants loop
                  Todo.Include (E);
                  Constant_Graph.Include_Vertex (E);
               end loop;
            end Seed;

         --  Start of processing for Resolve_Constants

         begin
            Constant_Graph := Constant_Graphs.Create;

            --  Add hardcoded representation of the variable input

            Constant_Graph.Add_Vertex (Variable_Input);

            --  Initialize the workset with constants in the generated globals
            --  ??? better to initialize this when globals are picked from the
            --  ALI.

            for Contr of Contracts loop
               Seed (Pick_Constants (Contr.Refined.Proof_Ins));
               Seed (Pick_Constants (Contr.Refined.Inputs));
               Seed (Pick_Constants (Contr.Initializes));
            end loop;

            --  Grow graph

            while not Todo.Is_Empty loop
               declare
                  E : constant Entity_Name := Todo (Todo.First);

                  Variable_Inputs : constant Name_Lists.List :=
                    (if Constant_Calls.Contains (E)
                     then Direct_Inputs_Of_Constant (E)
                     elsif Contracts.Contains (E)
                     then Direct_Inputs_Of_Subprogram (E)
                     else Name_Lists.Empty_List);

                  LHS : constant Constant_Graphs.Vertex_Id :=
                    Constant_Graph.Get_Vertex (E);

                  RHS : Constant_Graphs.Vertex_Id;

                  use type Constant_Graphs.Vertex_Id;

               begin
                  for Input of Variable_Inputs loop
                     RHS := Constant_Graph.Get_Vertex (Input);

                     if RHS = Constant_Graphs.Null_Vertex then
                        Constant_Graph.Add_Vertex (Input, RHS);
                        Todo.Insert (Input);
                     end if;

                     Constant_Graph.Add_Edge (LHS, RHS);
                  end loop;

                  Todo.Delete (E);
               end;
            end loop;

            --  Dump the graph before closing it

            Print (Constant_Graph);

            Constant_Graph.Close;
         end Resolve_Constants;

         --------------------------------
         -- Resolved_To_Variable_Input --
         --------------------------------

         function Resolved_To_Variable_Input
           (E              : Entity_Name;
            Constant_Graph : Constant_Graphs.Graph)
            return Boolean
         is
           (Constant_Graph.Edge_Exists (E, Variable_Input));

         ---------------------
         -- Strip_Constants --
         ---------------------

         procedure Strip_Constants
           (From           : in out Flow_Names;
            Constant_Graph :        Constant_Graphs.Graph)
         is

            procedure Strip (From : in out Global_Names);
            procedure Strip (From : in out Name_Sets.Set)
              with Post => From.Is_Subset (From'Old);

            -----------
            -- Strip --
            -----------

            procedure Strip (From : in out Global_Names) is
            begin
               Strip (From.Proof_Ins);
               Strip (From.Inputs);
            end Strip;

            procedure Strip (From : in out Name_Sets.Set) is
               Filtered : Name_Sets.Set;
            begin
               for E of From loop
                  if Constant_Calls.Contains (E) then
                     if Resolved_To_Variable_Input (E, Constant_Graph) then
                        Filtered.Insert (E);
                     end if;
                  else
                     Filtered.Insert (E);
                  end if;
               end loop;

               Name_Sets.Move (Target => From,
                               Source => Filtered);
            end Strip;

         --  Start of processing for Strip_Constants

         begin
            Strip (From.Proper);
            Strip (From.Refined);
            Strip (From.Initializes);
         end Strip_Constants;

      --  Start of processing for Resolve_Globals

      begin
         --  Library-level renamings have no root entity; ignore them
         if Present (Root_Entity)
           and then Gnat2Why_Args.Flow_Generate_Contracts
         then
            declare
               Position : Entity_Contract_Maps.Cursor;
               Inserted : Boolean;
            begin
               Global_Contracts.Insert
                 (Standard_Standard,
                  Position => Position,
                  Inserted => Inserted);
            end;

            declare
               Position : Phase_1_Info_Maps.Cursor;
               Inserted : Boolean;
            begin
               Phase_1_Info.Insert
                 (Standard_Standard,
                  Position => Position,
                  Inserted => Inserted);

               Phase_1_Info (Position).Kind := E_Package;
            end;

            --  Register entities from the current unit, even if they are not
            --  referenced. This is certainly needed for tasking-related checks
            --  on the root entity (if it is a "main subprogram"), but also
            --  seems reasonable for connecting ALI contracts for nested
            --  subprograms.

            Iterate_Main_Unit (Register_Entity'Access);

            Do_Global (Analyzed  => Standard_Standard,
                       Contracts => Global_Contracts);

            --  Only debug output from now on
            Debug_Traversal (Root_Entity);

            Dump_Main_Unit_Contracts
              (Highlight => To_Entity_Name (Root_Entity));

            --  Analyze_Remote_Calls;

            --  Remove edges leading to constants which do not have variable
            --  input.
            declare
               Constant_Graph : Constant_Graphs.Graph;

            begin
               Resolve_Constants (Global_Contracts, Constant_Graph);

               for C of Global_Contracts loop
                  Strip_Constants (C, Constant_Graph);
               end loop;
            end;
         end if;

      end Resolve_Globals;

      --  Now that the Globals Graph has been generated we set GG_Generated to
      --  True. We do this before we remove edges leading to constants without
      --  variable input. It is to use the generated globals when we call
      --  Get_Globals from within Has_Variable_Input.
      GG_Generated := True;

      --  Put tasking-related information back to the bag
      Process_Tasking_Graph;
      Print_Tasking_Info_Bag (GG_Phase_2);

      Note_Time ("gg_read - end");
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
     (E : Entity_Id) return Name_Sets.Set
   is
      EN : constant Entity_Name := To_Entity_Name (E);

      use Entity_Name_Graphs;

      Call_Graph : Graph renames Ceiling_Priority_Call_Graph;

      Res : Name_Sets.Set;
      V   : constant Vertex_Id := Call_Graph.Get_Vertex (EN);

      procedure Collect_Objects_From_Subprogram (S : Entity_Name);
      --  Collect protected objects directly accessed from subprogram S

      -------------------------------------
      -- Collect_Objects_From_Subprogram --
      -------------------------------------

      procedure Collect_Objects_From_Subprogram (S : Entity_Name) is
      begin
         declare
            Phase_1_Info : Name_Graphs.Map renames
              Tasking_Info_Bag (GG_Phase_1, Locks);

            C : constant Name_Graphs.Cursor := Phase_1_Info.Find (S);

         begin
            if Has_Element (C) then
               Res.Union (Phase_1_Info (C));
            end if;
         end;
      end Collect_Objects_From_Subprogram;

   --  Start of processing for Directly_Called_Protected_Objects

   begin
      --  Collect objects from the caller subprogram itself
      Collect_Objects_From_Subprogram (EN);

      --  and from all its callees
      for Obj of Call_Graph.Get_Collection (V, Out_Neighbours) loop
         declare
            Callee : constant Entity_Name := Call_Graph.Get_Key (Obj);
         begin
            Collect_Objects_From_Subprogram (Callee);
         end;
      end loop;

      --  For a (possibly) main subprogram we also consider protected objects
      --  that are accessed in elaborations.
      if E = Root_Entity
        and then Is_Subprogram (E)
        and then Might_Be_Main (E)
      then
         Res.Union (Directly_Called_POs_In_Elaborations);
      end if;

      return Res;
   end Directly_Called_Protected_Objects;

   ------------------------
   -- Find_In_Refinement --
   ------------------------

   function Find_In_Refinement (AS : Entity_Id; C : Entity_Id) return Boolean
   is
     (State_Comp_Map (To_Entity_Name (AS)).Contains (To_Entity_Name (C)));

   ----------------------
   -- Get_Constituents --
   ----------------------

   function Get_Constituents (E : Entity_Name) return Name_Sets.Set is
      C : constant Name_Graphs.Cursor := State_Comp_Map.Find (E);
   begin
      if Name_Graphs.Has_Element (C) then
         return State_Comp_Map (C);
      else
         return State_Part_Map (E).Union (Name_Sets.To_Set (E));
      end if;
   end Get_Constituents;

   ----------------------------
   -- GG_Encapsulating_State --
   ----------------------------

   function GG_Encapsulating_State (EN : Entity_Name) return Any_Entity_Name is
      C : Name_Maps.Cursor;
      use Name_Maps;
   begin
      C := Comp_State_Map.Find (EN);

      if Has_Element (C) then
         return Element (C);
      end if;

      C := Part_State_Map.Find (EN);

      if Has_Element (C) then
         return Element (C);
      end if;

      return Null_Entity_Name;
   end GG_Encapsulating_State;

   ---------------------------
   -- GG_Has_Been_Generated --
   ---------------------------

   function GG_Has_Been_Generated return Boolean is (GG_Generated);

   ----------------------------------------
   -- GG_State_Constituents_Map_Is_Ready --
   ----------------------------------------

   function GG_State_Constituents_Map_Is_Ready return Boolean
   is (GG_State_Constituents);

   ------------------------
   -- GG_Is_Ghost_Entity --
   ------------------------

   function GG_Is_Ghost_Entity (EN : Entity_Name) return Boolean
     renames Ghost_Entities.Contains;

   --------------------
   -- GG_Is_Constant --
   --------------------

   function GG_Is_Constant (EN : Entity_Name) return Boolean
     renames Constants.Contains;

   ----------------------
   -- GG_Is_CAE_Entity --
   ----------------------

   function GG_Is_CAE_Entity (EN : Entity_Name) return Boolean
     renames CAE_Entities.Contains;

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

   function GG_Is_Constituent (EN : Entity_Name) return Boolean is
     (Comp_State_Map.Contains (EN) or else Part_State_Map.Contains (EN));

   --------------------------------------
   -- GG_Is_Initialized_At_Elaboration --
   --------------------------------------

   function GG_Is_Initialized_At_Elaboration
     (EN : Entity_Name)
      return Boolean is
     (Initialized_Vars_And_States.Contains (EN)
        or else GG_Has_Async_Writers (EN));

   -----------------------
   -- GG_Is_Constituent --
   -----------------------

   function GG_Is_Part_Of_Constituent (EN : Entity_Name) return Boolean
     renames Part_State_Map.Contains;

   --------------------
   -- GG_Is_Volatile --
   --------------------

   function GG_Is_Volatile (EN : Entity_Name) return Boolean
     renames Volatile_Vars.Contains;

   ----------------------------------------
   -- Has_Potentially_Blocking_Statement --
   ----------------------------------------

   function Has_Potentially_Blocking_Statement (E : Entity_Id) return Boolean
   is
     (not Phase_1_Info (To_Entity_Name (E)).Nonblocking);

   ---------------------------------
   -- Potentially_Blocking_Callee --
   ---------------------------------

   function Potentially_Blocking_Callee
     (E : Entity_Id)
      return Any_Entity_Name
   is
      EN : constant Entity_Name := To_Entity_Name (E);
      --  Entity name, as it appears in the call graph

      use Entity_Name_Graphs;

      Caller : constant Vertex_Id :=
        Protected_Operation_Call_Graph.Get_Vertex (EN);
      --  Vertex that represents the analysed subprogram

      First_Callee : Any_Entity_Name := Null_Entity_Name;
      --  The potentially blocking callee, if any; if there are many, then we
      --  choose the one whose name is lexically first (to give the same
      --  results on different platforms, where hashes might not be reliable).

   begin
      for V of Protected_Operation_Call_Graph.
        Get_Collection (Caller, Out_Neighbours)
      loop
         declare
            Callee : constant Entity_Name :=
              Protected_Operation_Call_Graph.Get_Key (V);

         begin
            if not Is_Predefined (Callee)
               --  All user-defined callers of predefined potentially
               --  blocking subprograms have been already marked as
               --  potentially blocking, so here we can safely assume
               --  that any call to predefined subprogram is nonblocking.
              and then not Phase_1_Info (Callee).Nonblocking
            then
               if First_Callee = Null_Entity_Name then
                  First_Callee := Callee;
               elsif Lexical_Less (Callee, First_Callee) then
                  First_Callee := Callee;
               end if;
            end if;
         end;
      end loop;

      return First_Callee;
   end Potentially_Blocking_Callee;

   ----------------------------------------
   -- Potentially_Blocking_External_Call --
   ----------------------------------------

   function Potentially_Blocking_External_Call
     (E       : Entity_Id;
      Context : Entity_Id)
      return External_Call
   is
      EN : constant Entity_Name := To_Entity_Name (E);
      --  Entity name, as it appears in the call graph

      use Entity_Name_Graphs;

      Caller : constant Vertex_Id :=
        Protected_Operation_Call_Graph.Get_Vertex (EN);
      --  Vertex that represents the analysed subprogram

      function Calls_Same_Target_Type (S : Entity_Name) return Entity_Id;
      --  If subprogram S calls a protected operation of the protected type
      --  Context, then return the entity of that operation; otherwise, return
      --  Empty.

      ----------------------------
      -- Calls_Same_Target_Type --
      ----------------------------

      function Calls_Same_Target_Type (S : Entity_Name) return Entity_Id is
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
                 and then Scope (Callee_E) = Context
               then
                  return Callee_E;
               end if;
            end;

         end loop;

         return Empty;
      end Calls_Same_Target_Type;

   --  Start of processing for Potentially_Blocking_External_Call

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
            --  Check for external calls to a protected subprogram with
            --  the same target type as that of the protected action.
            if Callee_E = Empty
              or else not Scope_Within_Or_Same (Scope (Callee_E),
                                                Context)
            then
               declare
                  Protected_Subp : constant Entity_Id :=
                    Calls_Same_Target_Type (Callee);

               begin
                  if Present (Protected_Subp) then
                     return (Protected_Subprogram => Protected_Subp,
                             External_Callee      => Callee);
                  end if;
               end;
            end if;
         end;

      end loop;

      return (Protected_Subprogram => Empty,
              External_Callee      => Null_Entity_Name);
   end Potentially_Blocking_External_Call;

   ------------------------------------------
   -- Is_Potentially_Nonreturning_Internal --
   ------------------------------------------

   function Is_Potentially_Nonreturning_Internal (EN : Entity_Name)
                                                  return Boolean
   is

      function Calls_Potentially_Nonreturning_Subprogram return Boolean;
      --  Returns True iff the called subprogram, the callee, is potentially
      --  nonreturning.

      -----------------------------------------------
      -- Calls_Potentially_Nonreturning_Subprogram --
      -----------------------------------------------

      function Calls_Potentially_Nonreturning_Subprogram return Boolean is
         use Entity_Name_Graphs;

         Caller : constant Vertex_Id :=
           Termination_Call_Graph.Get_Vertex (EN);
         --  Vertex that represents the analyzed subprogram

      begin
         for V of Termination_Call_Graph.
           Get_Collection (Caller, Out_Neighbours)
         loop
            declare
               Callee : constant Entity_Name :=
                 Termination_Call_Graph.Get_Key (V);
            begin
               --  We say that the caller calls a potentially nonreturning
               --  subprogram if the callee does not have the Terminating
               --  annotation and:
               --  * has already been detected as potentially nonreturning
               --    in phase 1 (is contained in Nonreturning_Subprograms)
               --  * is recursive.
               if not (Phase_1_Info.Contains (Callee)
                       and then Phase_1_Info (Callee).Has_Terminate)
                 and then Is_Directly_Nonreturning (Callee)
               then
                  return True;
               end if;
            end;
         end loop;
         return False;
      end Calls_Potentially_Nonreturning_Subprogram;

   --  Start of processing for Is_Potentially_Nonreturning

   begin
      --  Returns True if it has been registered as nonreturning in phase 1
      --  (see usage of GG_Register_Nonreturning in flow.adb), is recursive or
      --  calls a potentially nonreturning subprogram. The latter is checked
      --  using a call graph where vertexes are subprograms and edges
      --  represents subprogram calls.
      --  Always returns False if the subprogram has been annotated with the
      --  Terminating annotation, which is also detected in phase 1 (see
      --  GG_Register_Terminating).
      return Is_Directly_Nonreturning (EN)
        or else Calls_Potentially_Nonreturning_Subprogram;
   end Is_Potentially_Nonreturning_Internal;

   function Is_Potentially_Nonreturning_Internal (E : Entity_Id)
                                                  return Boolean
   is
     (Is_Potentially_Nonreturning_Internal (To_Entity_Name (E)));

   ---------------------------------
   -- Is_Potentially_Nonreturning --
   ---------------------------------

   function Is_Potentially_Nonreturning (E : Entity_Id) return Boolean is
     (not Has_Terminate_Annotation (E)
      and then Is_Potentially_Nonreturning_Internal (E));

   ------------------
   -- Is_Recursive --
   ------------------

   function Is_Recursive (EN : Entity_Name) return Boolean is
     (Subprogram_Call_Graph.Contains (EN)
      and then Subprogram_Call_Graph.Edge_Exists (EN, EN));

   function Is_Recursive (E : Entity_Id) return Boolean is
     (Is_Recursive (To_Entity_Name (E)));

   ------------------------
   -- Mutually_Recursive --
   ------------------------

   function Mutually_Recursive (EN1, EN2 : Entity_Name) return Boolean is
     (Subprogram_Call_Graph.Contains (EN1)
      and then Subprogram_Call_Graph.Contains (EN2)
      and then Subprogram_Call_Graph.Edge_Exists (EN1, EN2)
      and then Subprogram_Call_Graph.Edge_Exists (EN2, EN1));

   function Mutually_Recursive (E1, E2 : Entity_Id) return Boolean is
     (Mutually_Recursive (To_Entity_Name (E1), To_Entity_Name (E2)));

   ------------------------
   -- Calls_Current_Task --
   ------------------------

   function Calls_Current_Task (E : Entity_Id) return Boolean is
     (Protected_Operation_Call_Graph.Contains (Current_Task)
        and then Protected_Operation_Call_Graph.Edge_Exists
          (To_Entity_Name (E), Current_Task));

   -----------------------
   -- Refinement_Exists --
   -----------------------

   function Refinement_Exists (AS : Entity_Id) return Boolean is
     (State_Comp_Map.Contains (To_Entity_Name (AS)));

   ------------------------------
   -- GG_Expand_Abstract_State --
   ------------------------------

   function GG_Expand_Abstract_State (AS : Entity_Name) return Name_Sets.Set is
      Constituents : Name_Sets.Set;

   begin
      if State_Comp_Map.Contains (AS) then
         for C of State_Comp_Map (AS) loop
            Constituents.Union (GG_Expand_Abstract_State (C));
         end loop;
      elsif State_Part_Map.Contains (AS) then
         for C of State_Part_Map (AS) loop
            Constituents.Union (GG_Expand_Abstract_State (C));
         end loop;

         Constituents.Insert (AS);
      else
         Constituents.Insert (AS);
      end if;

      return Constituents;
   end GG_Expand_Abstract_State;

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

      Task_Instances (C).Insert (Object);
   end Register_Task_Object;

   ---------------------
   -- Tasking_Objects --
   ---------------------

   function Tasking_Objects
     (Kind : Tasking_Owning_Kind;
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

   ----------------------------
   -- Is_Protected_Operation --
   ----------------------------

   function Is_Protected_Operation (E_Name : Entity_Name) return Boolean is
      C : constant Phase_1_Info_Maps.Cursor := Phase_1_Info.Find (E_Name);
   begin
      if Phase_1_Info_Maps.Has_Element (C) then
         declare
            Info : Partial_Contract renames Phase_1_Info (C);
         begin
            return
              (case Info.Kind is
                  when Entry_Kind               => True,
                  when E_Function | E_Procedure => Info.Is_Protected,
                  when others                   => False);
         end;
      else
         return False;
      end if;
   end Is_Protected_Operation;

   ----------------------
   -- Categorize_Calls --
   ----------------------

   function Categorize_Calls
     (EN        : Entity_Name;
      Contracts : Entity_Contract_Maps.Map)
      return Call_Names
   is
      Original : Call_Names renames Contracts (EN).Calls;

      O_Proof, O_Conditional, O_Definite : Name_Sets.Set;

   begin
      Find_Definitive_Calls : declare
         Todo : Name_Sets.Set := Original.Definite_Calls;
         Done : Name_Sets.Set;

      begin
         loop
            if not Todo.Is_Empty then
               declare
                  Pick : constant Entity_Name :=
                    Name_Sets.Element (Todo.First);

               begin
                  Done.Insert (Pick);

                  if Contracts.Contains (Pick) then
                     Todo.Union (Contracts (Pick).Calls.Definite_Calls - Done);
                  end if;

                  Todo.Delete (Pick);
               end;
            else
               exit;
            end if;
         end loop;

         pragma Assert (Original.Definite_Calls.Is_Subset (Of_Set => Done));

         Name_Sets.Move (Target => O_Definite,
                         Source => Done);
      end Find_Definitive_Calls;

      Find_Conditional_Calls : declare
         type Calls is record
            Conditional, Definite : Name_Sets.Set;
         end record;

         Todo : Calls := (Conditional => Original.Conditional_Calls,
                          Definite    => Original.Definite_Calls);

         Done : Calls;

      begin
         loop
            if not Todo.Conditional.Is_Empty then
               declare
                  Pick : constant Entity_Name :=
                    Name_Sets.Element (Todo.Conditional.First);

               begin
                  Done.Conditional.Insert (Pick);

                  if Contracts.Contains (Pick) then
                     declare
                        Picked : Call_Names renames Contracts (Pick).Calls;

                     begin
                        Todo.Conditional.Union
                          ((Picked.Conditional_Calls or Picked.Definite_Calls)
                           - Done.Conditional);
                     end;
                  end if;

                  Todo.Conditional.Delete (Pick);
               end;
            elsif not Todo.Definite.Is_Empty then
               declare
                  Pick : constant Entity_Name :=
                    Name_Sets.Element (Todo.Definite.First);

               begin
                  Done.Definite.Insert (Pick);

                  if Contracts.Contains (Pick) then
                     declare
                        Picked : Call_Names renames Contracts (Pick).Calls;

                     begin
                        Todo.Conditional.Union
                          (Picked.Conditional_Calls - Done.Conditional);

                        Todo.Definite.Union
                          (Picked.Definite_Calls - Done.Definite);
                     end;
                  end if;

                  Todo.Definite.Delete (Pick);
               end;
            else
               exit;
            end if;
         end loop;

         pragma Assert
           (Original.Conditional_Calls.Is_Subset (Of_Set => Done.Conditional));

         Name_Sets.Move (Target => O_Conditional,
                         Source => Done.Conditional);
      end Find_Conditional_Calls;

      Find_Proof_Calls : declare
         type Calls is record
            Proof, Other : Name_Sets.Set;
         end record;

         Todo : Calls := (Proof => Original.Proof_Calls,
                          Other => Original.Conditional_Calls or
                                   Original.Definite_Calls);

         Done : Calls;

      begin
         loop
            if not Todo.Proof.Is_Empty then
               declare
                  Pick : constant Entity_Name :=
                    Name_Sets.Element (Todo.Proof.First);

               begin
                  Done.Proof.Insert (Pick);

                  if Contracts.Contains (Pick) then
                     declare
                        Picked : Call_Names renames Contracts (Pick).Calls;

                     begin
                        Todo.Proof.Union
                          ((Picked.Proof_Calls or
                            Picked.Conditional_Calls or
                            Picked.Definite_Calls)
                           - Done.Proof);
                     end;
                  end if;

                  Todo.Proof.Delete (Pick);
               end;
            elsif not Todo.Other.Is_Empty then
               declare
                  Pick : constant Entity_Name :=
                    Name_Sets.Element (Todo.Other.First);

               begin
                  Done.Other.Insert (Pick);

                  if Contracts.Contains (Pick) then
                     declare
                        Picked : Call_Names renames Contracts (Pick).Calls;

                     begin
                        Todo.Proof.Union
                          (Picked.Proof_Calls - Done.Proof);

                        Todo.Other.Union
                          ((Picked.Conditional_Calls or
                            Picked.Definite_Calls)
                           - Done.Other);
                     end;
                  end if;

                  Todo.Other.Delete (Pick);
               end;
            else
               exit;
            end if;
         end loop;

         pragma Assert (Original.Proof_Calls.Is_Subset (Of_Set => Done.Proof));

         Name_Sets.Move (Target => O_Proof,
                         Source => Done.Proof);
      end Find_Proof_Calls;

      return (Proof_Calls       => O_Proof - O_Conditional - O_Definite,
              Conditional_Calls => O_Conditional,
              Definite_Calls    => O_Definite - O_Conditional);
   end Categorize_Calls;

   -------
   -- < --
   -------

   function "<" (Left, Right : Task_Object) return Boolean is

      function Compare_Names return Boolean;
      --  Returns the result of comparing names of Left and Right; to be used
      --  as a last resort.

      -------------------
      -- Compare_Names --
      -------------------

      function Compare_Names return Boolean is
        (To_String (Left.Name) < To_String (Right.Name));

      --  Local variables
      Has_Left_Node  : constant Boolean := Present (Left.Node);
      Has_Right_Node : constant Boolean := Present (Right.Node);

      --  Start of processing for "<"

   begin
      if Has_Left_Node
        and then Has_Right_Node
      then
         declare
            Left_In_Analyzed : constant Boolean :=
              Is_In_Analyzed_Files (Left.Node);

            Right_In_Analyzed : constant Boolean :=
              Is_In_Analyzed_Files (Right.Node);

         begin
            return (if Left_In_Analyzed and Right_In_Analyzed then
                      Left.Node < Right.Node
                    elsif Left_In_Analyzed then
                      True
                    elsif Right_In_Analyzed then
                      False
                    else
                      Compare_Names);
         end;
      elsif Has_Left_Node then
         return True;
      elsif Has_Right_Node then
         return False;
      else
         return Compare_Names;
      end if;
   end "<";

   -----------
   -- Print --
   -----------

   procedure Print (G : Constant_Graphs.Graph)
   is
      use Constant_Graphs;

      function NDI (G : Graph; V : Vertex_Id) return Node_Display_Info;
      --  Pretty-printing for vertices in the dot output

      function EDI
        (G      : Graph;
         A      : Vertex_Id;
         B      : Vertex_Id;
         Marked : Boolean;
         Colour : No_Colours) return Edge_Display_Info;
      --  Pretty-printing for edges in the dot output

      ---------
      -- NDI --
      ---------

      function NDI (G : Graph; V : Vertex_Id) return Node_Display_Info
      is
         E : constant Entity_Name := G.Get_Key (V);
      begin
         if E = Variable_Input then
            return (Show        => True,
                    Shape       => Node_Shape_T'First,
                    Colour      => Null_Unbounded_String,
                    Fill_Colour => To_Unbounded_String ("gray"),
                    Label       => To_Unbounded_String ("Variable input"));
         else
            return (Show        => True,
                    Shape       => (if Constant_Calls.Contains (E)
                                    then Shape_Oval
                                    else Shape_Box),
                    Colour      => Null_Unbounded_String,
                    Fill_Colour => Null_Unbounded_String,
                    Label       => To_Unbounded_String (To_String (E)));
         end if;
      end NDI;

      ---------
      -- EDI --
      ---------

      function EDI
        (G      : Graph;
         A      : Vertex_Id;
         B      : Vertex_Id;
         Marked : Boolean;
         Colour : No_Colours) return Edge_Display_Info
      is
         pragma Unreferenced (G, A, B, Marked, Colour);
      begin
         return
           (Show   => True,
            Shape  => Edge_Normal,
            Colour => Null_Unbounded_String,
            Label  => Null_Unbounded_String);
      end EDI;

      --  Local constants

      Filename : constant String :=
        Unique_Name (Unique_Main_Unit_Entity) & "_constants_2";

   --  Start of processing for Print_Graph

   begin
      if Gnat2Why_Args.Flow_Advanced_Debug then
         G.Write_Pdf_File
           (Filename  => Filename,
            Node_Info => NDI'Access,
            Edge_Info => EDI'Access);
      end if;
   end Print;

   ------------------
   -- Down_Project --
   ------------------

   function Down_Project
     (G      : Global_Names;
      Caller : Entity_Name)
      return Global_Names
   is
     (Proof_Ins => Down_Project (G.Proof_Ins, Caller),
      Inputs    => Down_Project (G.Inputs,    Caller),
      Outputs   => Down_Project (G.Outputs,   Caller));

   function Down_Project
     (Vars   : Name_Sets.Set;
      Caller : Entity_Name)
      return Name_Sets.Set
   is
      Projected : Name_Sets.Set;
   begin
      for Var of Vars loop
         Projected.Union (Down_Project (Var, Caller));
      end loop;

      return Projected;
   end Down_Project;

   function Down_Project
     (Var    : Entity_Name;
      Caller : Entity_Name)
      return Name_Sets.Set
   is
      Target_Scope : constant Name_Scope :=
        (Ent => Caller, Part => Body_Part);

   begin
      if Is_Heap_Variable (Var) then
         return Name_Sets.To_Set (Var);
      else
         if State_Abstractions.Contains (Var) then

            --  ??? recursive call to Down_Project?

            if State_Refinement_Is_Visible (Var, Target_Scope) then
               return State_Comp_Map (Var);
            elsif Part_Of_Is_Visible (Var, Target_Scope) then
               if State_Part_Map.Contains (Var) then
                  return Name_Sets.Union
                    (State_Part_Map (Var),
                     Name_Sets.To_Set (Var));
               else
                  return Name_Sets.To_Set (Var);
               end if;
            else
               return Name_Sets.To_Set (Var);
            end if;
         else
            return Name_Sets.To_Set (Var);
         end if;
      end if;
   end Down_Project;

   ------------------------
   -- Is_Fully_Contained --
   ------------------------

   function Is_Fully_Contained (State   : Entity_Name;
                                Outputs : Name_Sets.Set;
                                Scop    : Name_Scope)
                                return Boolean
   is
     (Name_Sets.Is_Subset (Subset => Down_Project (State, Scop.Ent),
                           Of_Set => Outputs));

   ----------------
   -- Up_Project --
   ----------------

   procedure Up_Project (Vars       :     Name_Sets.Set;
                         Scope      :     Name_Scope;
                         Projected  : out Name_Sets.Set;
                         Partial    : out Name_Sets.Set)
   is
   begin
      Projected.Clear;
      Partial.Clear;

      for Var of Vars loop
         if GG_Is_Constituent (Var) then

            --  We project depending on whether the constituent is visible (and
            --  not its enclosing state refinement), because when projecting
            --  to a private part of a package spec where that constituent
            --  is declared (as a Part_Of an abstract state) we want the
            --  constituent, which is the most precise result we can get.

            declare
               State : constant Entity_Name := GG_Encapsulating_State (Var);

            begin
               if State_Refinement_Is_Visible (State, Scope)
                 or else (GG_Is_Part_Of_Constituent (Var)
                          and then Part_Of_Is_Visible (State, Scope))
               then
                  Projected.Include (Var);
               else
                  Partial.Include (State);
               end if;
            end;
         else
            Projected.Include (Var);
         end if;
      end loop;
   end Up_Project;

   procedure Up_Project (Vars           :     Global_Names;
                         Projected_Vars : out Global_Names;
                         Scope          :     Name_Scope)
   is
      --  ??? the following code for up-projecting generated Refined_Global
      --  has much in common with code for up-projecting Refined_Depends;
      --  they should be refactored.

      function Visible_View (E : Entity_Name) return Entity_Name;
      --  Return the most precise representation of F visible from Scope

      procedure Add_Mapping (Item : Entity_Name);
      --  Add mapping from Item to its most precise representation

      Visible_Views  : Name_Sets.Set;
      Projection_Map : Name_Maps.Map;

      -----------------
      -- Add_Mapping --
      -----------------

      procedure Add_Mapping (Item : Entity_Name) is
         Repr : constant Entity_Name := Visible_View (Item);

      begin
         Projection_Map.Insert (Key      => Item,
                                New_Item => Repr);

         Visible_Views.Include (Repr);
      end Add_Mapping;

      ------------------
      -- Visible_View --
      ------------------

      function Visible_View (E : Entity_Name) return Entity_Name is
         Projected, Partial : Name_Sets.Set;

         use type Ada.Containers.Count_Type;

      begin
         if GG_Is_Constituent (E) then
            Up_Project (Name_Sets.To_Set (E), Scope, Projected, Partial);
            pragma Assert (Partial.Length + Projected.Length = 1);

            return (if Projected.Is_Empty
                    then Partial (Partial.First)
                    else Projected (Projected.First));
         else
            return E;
         end if;
      end Visible_View;

   --  Start of processing of Up_Project

   begin
      --  First, up-project all globals to their most precise representation
      --  that is visible from Scope.

      for Item of Vars.Proof_Ins loop
         Add_Mapping (Item);
      end loop;

      for Item of Vars.Inputs loop
         Add_Mapping (Item);
      end loop;

      for Item of Vars.Outputs loop
         if not Vars.Inputs.Contains (Item) then
            Add_Mapping (Item);
         end if;
      end loop;

      --  The most precise representation might violate SPARK RM 7.2.6(7), i.e.
      --  we might get both a constituent and its encapsulating abstract state.
      --  We climb the abstract state hierarchy and if we get an abstract
      --  state that appears in the contract we subsitute the target with
      --  that abstract state.

      for Mapping in Projection_Map.Iterate loop
         declare
            Source : Entity_Name renames Name_Maps.Key (Mapping);
            Target : Entity_Name renames Projection_Map (Mapping);

            pragma Unreferenced (Source);
            --  This is for debug

            Repr : Entity_Name := Target;

         begin
            while GG_Is_Constituent (Repr) loop
               Repr := GG_Encapsulating_State (Repr);
               if True then --  ??? Present (Repr)
                  if Visible_Views.Contains (Repr) then
                     Target := Repr;
                  end if;
               else
                  exit;
               end if;
            end loop;
         end;
      end loop;

      --  Inputs are straightforward to up-project

      for Item of Vars.Inputs loop
         Projected_Vars.Inputs.Include (Projection_Map (Item));
      end loop;

      for Item of Vars.Outputs loop
         declare
            Projected_Item : Entity_Name renames Projection_Map (Item);
         begin
            --  If a global output was up-projected to an abstract state and
            --  this state is not fully written, then it must be added to
            --  projected inputs.
            if Item /= Projected_Item
              and then not Is_Fully_Contained (Projected_Item,
                                               Vars.Outputs,
                                               Scope)
            then
               Projected_Vars.Inputs.Include (Projected_Item);
            end if;

            Projected_Vars.Outputs.Include (Projected_Item);
         end;
      end loop;

      for Item of Vars.Proof_Ins loop
         declare
            Projected_Item : Entity_Name renames Projection_Map (Item);
         begin
            --  Projected proof_ins must not duplicate projected inputs and
            --  outputs.
            if not Projected_Vars.Inputs.Contains (Projected_Item)
              and then not Projected_Vars.Outputs.Contains (Projected_Item)
            then
               Projected_Vars.Proof_Ins.Include (Projected_Item);
            end if;
         end;
      end loop;

   end Up_Project;

   ---------------------------
   -- Expand_Abstract_State --
   ---------------------------

   function Expand_Abstract_State (F : Flow_Id) return Flow_Id_Sets.Set is
   begin
      --  Abstract state is expanded as much as possible using refinement
      --  recorded in the ALI file.

      if Is_Abstract_State (F) then
         declare
            State : constant Entity_Name :=
              (if F.Kind = Direct_Mapping
               then To_Entity_Name (F.Node)
               else F.Name);

            Expanded : Flow_Id_Sets.Set;

         begin
            if State_Comp_Map.Contains (State) then
               for C of State_Comp_Map (State) loop
                  Expanded.Union (Expand_Abstract_State (Get_Flow_Id (C)));
               end loop;
            elsif State_Part_Map.Contains (State) then
               for C of State_Part_Map (State) loop
                  Expanded.Union (Expand_Abstract_State (Get_Flow_Id (C)));
               end loop;

               Expanded.Insert (Magic_String_Id (State));
            else
               --  Expand Part_Of constituents that are not known to "generated
               --  globals" machinery, e.g. because they appear in the (down
               --  projected) Pre/Post of subprograms from external units.

               if F.Kind = Direct_Mapping then
                  for C of Iter (Part_Of_Constituents (F.Node)) loop
                     Expanded.Union
                       (Expand_Abstract_State (Direct_Mapping_Id (C)));
                  end loop;
               end if;

               Expanded.Insert (Magic_String_Id (State));
            end if;

            return Expanded;
         end;

      --  Other objects are merely converted to the proof view convention

      else
         case F.Kind is
            when Direct_Mapping =>
               declare
                  E : constant Entity_Id := Get_Direct_Mapping_Id (F);

               begin
                  --  Entities in SPARK are represented by Entity_Id; those
                  --  not in SPARK are represented by Entity_Name, because
                  --  they behave as "blobs".

                  return Flow_Id_Sets.To_Set
                    (if Entity_In_SPARK (E)
                     then Change_Variant (F, Normal_Use)
                     else Magic_String_Id (To_Entity_Name (E)));
               end;

            when Magic_String =>
               return Flow_Id_Sets.To_Set (Change_Variant (F, Normal_Use));

            when Null_Value =>
               return Flow_Id_Sets.Empty_Set;

            when others =>
               raise Program_Error;
         end case;
      end if;
   end Expand_Abstract_State;

end Flow_Generated_Globals.Phase_2;
