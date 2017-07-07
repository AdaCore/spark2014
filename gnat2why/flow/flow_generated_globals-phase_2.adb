------------------------------------------------------------------------------
--                                                                          --
--                           GNAT2WHY COMPONENTS                            --
--                                                                          --
--       F L O W . G E N E R A T E D _ G L O B A L S . P H A S E _ 2        --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--               Copyright (C) 2014-2017, Altran UK Limited                 --
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
with Ada.Containers.Doubly_Linked_Lists;
with Ada.Strings.Fixed;
with Ada.Strings.Unbounded;      use Ada.Strings.Unbounded;
with Ada.Text_IO;                use Ada.Text_IO;

with ALI;                        use ALI;
with Lib;                        use Lib;
with Namet;                      use Namet;
with Osint;                      use Osint;
with Output;                     use Output;
with Sem_Util;                   use Sem_Util;

with Call;                       use Call;
with Debug.Timing;               use Debug.Timing;
with Gnat2Why.Annotate;          use Gnat2Why.Annotate;
with Gnat2Why_Args;
with SPARK2014VSN;               use SPARK2014VSN;
with SPARK_Frame_Conditions;     use SPARK_Frame_Conditions;
with SPARK_Util;                 use SPARK_Util;
with SPARK_Xrefs;                use SPARK_Xrefs;

with Flow_Refinement;            use Flow_Refinement;
with Flow_Utility;               use Flow_Utility;
with Graphs;
with Flow_Generated_Globals.Traversal; use Flow_Generated_Globals.Traversal;

with Flow_Generated_Globals.ALI_Serialization;
use Flow_Generated_Globals.ALI_Serialization;

package body Flow_Generated_Globals.Phase_2 is

   GG_Generated : Boolean := False;
   --  Set to True by GG_Read once the Global Graph has been generated.

   GG_State_Constituents : Boolean := False;
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
     To_Entity_Name ("ada__task_identification__current_task");
   --  This will be used when checking for calls to Current_Task

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
      Entity  : Entity_Name;

      Proper  : Global_Names;
      Refined : Global_Names;

      Initializes : Name_Sets.Set;
      --  Only meaningful for packages
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

   Debug_Print_Generated_Initializes : constant Boolean := False;
   --  Enables printing of the generated initializes aspects

   ----------------------------------------------------------------------
   --  State information
   ----------------------------------------------------------------------

   State_Comp_Map : Name_Graphs.Map := Name_Graphs.Empty_Map;
   --  Mapping from abstract states to their constituents, i.e.
   --  abstract_state -> {constituents}

   Comp_State_Map : Name_Maps.Map   := Name_Maps.Empty_Map;
   --  A reverse of the above mapping, i.e. constituent -> abstract_state

   State_Abstractions : Name_Sets.Set := Name_Sets.Empty_Set;
   --  State abstractions that the GG knows of

   ----------------------------------------------------------------------
   --  Initializes information
   ----------------------------------------------------------------------

   type Initializes_Info is record
      LHS       : Name_Sets.Set;
      LHS_Proof : Name_Sets.Set;
      RHS       : Name_Sets.Set;
      RHS_Proof : Name_Sets.Set;
   end record;

   package Initializes_Aspects_Maps is new Ada.Containers.Hashed_Maps
     (Key_Type        => Entity_Name,
      Element_Type    => Initializes_Info,
      Hash            => Name_Hash,
      Equivalent_Keys => "=");

   Initializes_Aspects : Initializes_Aspects_Maps.Map;

   Initialized_Vars_And_States : Name_Sets.Set;
   --  Variables and state abstractions know to be initialized

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

   function Scope (EN : Entity_Name) return Entity_Name;
   --  Equivalent of Sinfo.Scope for entity names

   function Scope_Within_Or_Same (Scope1, Scope2 : Entity_Name) return Boolean;
   --  Equivalent of Sem_Util.Scope_Within_Or_Same for entity names;
   --  ??? see Scope_Truly_Within_Or_Same and make this one work for subunits

   function Is_Predefined (EN : Entity_Name) return Boolean;
   --  Returns True iff EN is a predefined entity

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
   --  Distinguishes between simple vars and constituents. For constituents,
   --  it checks if they are visible and if they are NOT it checks if their
   --  encapsulating state is. If the encapsulating state is visible then
   --  return that (otherwise repeat the process). When Processing_Writes is
   --  set, we also check if all constituents are used and if they are not we
   --  also add them on the Reads set.

   function Generated_Calls (Caller : Entity_Name) return Name_Sets.Set;
   --  Returns callees of a Caller

   function Is_Potentially_Nonreturning_Internal (EN : Entity_Name)
                                                  return Boolean;
   --  See comment for Is_Potentially_Nonreturning with Entity_Id as an input

   function Is_Recursive (EN : Entity_Name) return Boolean;
   --  Returns True iff there is an edge in the subprogram call graph that
   --  connects a subprogram to itself.

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

   ----------------------------------------------------------------------
   --  Debug routines
   ----------------------------------------------------------------------

   procedure Print (G : Constant_Graphs.Graph);
   --  Print graph with dependencies between constants and their inputs

   procedure Print_Tasking_Info_Bag (P : Phase);
   --  Display the tasking-related information

   procedure Print_Generated_Initializes_Aspects;
   --  Prints all the generated initializes aspects

   procedure Print_Name_Set (Header : String; Set : Name_Sets.Set);
   --  Print Header followed by elements of Set

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
         Direct_Calls.Append (Find_Entity (Callee));
      end loop;
      return Direct_Calls;
   end Generated_Calls;

   -------------------------------
   -- GG_Get_State_Abstractions --
   -------------------------------

   function GG_Get_State_Abstractions return Name_Sets.Set is
   begin
      return State_Abstractions;
   end GG_Get_State_Abstractions;

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

      procedure Populate_Results (G : Global_Names);

      procedure Down_Project (Vars : in out Flow_Id_Sets.Set);
      --  ??? In other code (which perhaps should be deleted) this is called
      --  Expand; we should decide on a single name. Also, this should be
      --  a function.

      ------------------
      -- Down_Project --
      ------------------

      procedure Down_Project (Vars : in out Flow_Id_Sets.Set) is
         Projected : Flow_Id_Sets.Set;

      begin
         for Var of Vars loop
            case Var.Kind is
               when Direct_Mapping =>
                  --  ??? this expression involves a lot of unnecessary
                  --  conversions; this is the price for broken API.
                  Projected.Union
                    (Change_Variant
                       (To_Flow_Id_Set
                          (Flow_Refinement.Down_Project
                             (Get_Direct_Mapping_Id (Var), S)),
                       Variant => Var.Variant));

               when Magic_String =>
                  Projected.Insert (Var);

               when others =>
                  raise Program_Error;
            end case;
         end loop;

         Flow_Id_Sets.Move (Target => Vars,
                            Source => Projected);
      end Down_Project;

      ----------------------
      -- Populate_Results --
      ----------------------

      procedure Populate_Results (G : Global_Names) is
      begin
         Globals.Proof_Ins := To_Flow_Id_Set (G.Proof_Ins, View => In_View);
         Globals.Reads     := To_Flow_Id_Set (G.Inputs,    View => In_View);
         Globals.Writes    := To_Flow_Id_Set (G.Outputs,   View => Out_View);
      end Populate_Results;

   --  Start of processing for GG_Get_Globals

   begin
      if Entity_Contract_Maps.Has_Element (C) then
         Populate_Results
           (if Subprogram_Refinement_Is_Visible (E, S)
            then Global_Contracts (C).Refined
            else Global_Contracts (C).Proper);

         --  Down-project globals to the scope of the caller

         Down_Project (Globals.Proof_Ins);
         Down_Project (Globals.Reads);
         Down_Project (Globals.Writes);
      else
         Globals.Proof_Ins.Clear;
         Globals.Reads.Clear;
         Globals.Writes.Clear;

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

   function GG_Get_Initializes
     (E : Entity_Id;
      S : Flow_Scope)
      return Dependency_Maps.Map
   is
      C : constant Initializes_Aspects_Maps.Cursor :=
        Initializes_Aspects.Find (To_Entity_Name (E));
      --  Position of the Initializes aspect for E, if any

   begin
      if Initializes_Aspects_Maps.Has_Element (C) then
         --  Retrieve the relevant Name_Dependency_Map, up project it to S and
         --  then convert it into a Dependency_Map.
         declare
            LHS_Scope : constant Flow_Scope := (Ent  => E,
                                                Part => Visible_Part);

            II : Initializes_Info renames Initializes_Aspects (C);

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

            return DM : Dependency_Maps.Map do
               --  Add regular variables
               for F of FS_LHS loop
                  DM.Insert (F, FS_RHS);
               end loop;

               --  Add proof variables
               for F of FS_LHS_Proof loop
                  DM.Insert (F, FS_RHS_Proof);
               end loop;
            end return;
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

   function GG_Get_Local_Variables (E : Entity_Id) return Name_Sets.Set is
      C : constant Phase_1_Info_Maps.Cursor :=
        Phase_1_Info.Find (To_Entity_Name (E));

   begin
      if Phase_1_Info_Maps.Has_Element (C) then
         declare
            Info : Partial_Contract renames Phase_1_Info (C);
         begin
            return Info.Local_Variables or Info.Local_Ghost_Variables;
         end;
      else
         return Name_Sets.Empty_Set;
      end if;
   end GG_Get_Local_Variables;

   -------------------
   -- Is_Predefined --
   -------------------

   function Is_Predefined (EN : Entity_Name) return Boolean is
   begin
      return Match (Predefined, To_String (EN));
   end Is_Predefined;

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

      function Fully_Refine (EN : Entity_Name) return Name_Sets.Set;
      --  Returns the most refined constituents of variable or state
      --  abstraction.

      ------------------
      -- Fully_Refine --
      ------------------

      function Fully_Refine (EN : Entity_Name) return Name_Sets.Set is
         Refined : Name_Sets.Set;

         procedure Refine (State : Entity_Name);
         --  Recursively refine state into its constituents

         ------------
         -- Refine --
         ------------

         procedure Refine (State : Entity_Name) is
            Constituents : constant Name_Graphs.Cursor :=
              State_Comp_Map.Find (State);
         begin
            if Name_Graphs.Has_Element (Constituents) then
               for Constituent of State_Comp_Map (Constituents) loop
                  Refine (Constituent);
               end loop;
            else
               Refined.Insert (State);
            end if;
         end Refine;

      --  Start of processing for Fully_Refine

      begin
         Refine (EN);

         return Refined;
      end Fully_Refine;

   --  Start of processing for Up_Project

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
               Enclosing_State := GG_Encapsulating_State (Var_Name);

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
            if not Constituents.Is_Subset (Of_Set => Most_Refined) then
               Reads.Include (Get_Flow_Id (AS, In_View));
            end if;
         end;
      end loop;
   end Up_Project;

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
               if (case Ekind (E) is
                      when E_Entry | E_Task_Type =>
                         True,
                      when E_Function | E_Procedure =>
                         Ekind (Scope (E)) = E_Protected_Type
                         or else Might_Be_Main (E),
                      when others =>
                         False)
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
            A : Archive (Serialisation.Input) :=
              From_String (Line (Line'First + 3 .. Line'Last));

            V : ALI_Entry := (Kind => EK_Error);

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

         --  Parse_GG_Line

         begin
            Serialize (A, V);
            case V.Kind is
               when EK_Error =>
                  Corrupted_ALI_File ("parse error");

               when EK_End_Marker =>
                  if GG_Parsing_State = Started then
                     GG_Parsing_State := Finished;
                  else
                     Corrupted_ALI_File ("unexpected GG end marker");
                  end if;

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
                        State_Comp_Map (State).Insert (V.The_Constituents (C));

                        Comp_State_Map.Insert (V.The_Constituents (C),
                                               V.The_State);

                        Name_Lists.Next (C);
                     end loop;
                  end;

                  State_Abstractions.Include (V.The_State);

               when EK_Remote_States =>
                  State_Abstractions.Union (V.The_Remote_States);

               when EK_Volatiles =>
                  Async_Writers_Vars.Union (V.The_Async_Writers);
                  Volatile_Vars.Union (V.The_Async_Writers);

                  Async_Readers_Vars.Union (V.The_Async_Readers);
                  Volatile_Vars.Union (V.The_Async_Readers);

                  Effective_Reads_Vars.Union (V.The_Effective_Reads);
                  Volatile_Vars.Union (V.The_Effective_Reads);

                  Effective_Writes_Vars.Union (V.The_Effective_Writes);
                  Volatile_Vars.Union (V.The_Effective_Writes);

               when EK_Globals =>
                  --  ??? this line should be loaded only when
                  --  For_Current_Unit or else not V.The_Global_Info.Local

                  --  Move global information to separate container
                  Global_Contracts.Insert
                    (Key      => V.The_Global_Info.Name,
                     New_Item => V.The_Global_Info.Globals);

                  --  ??? Clear the original map as a sanity check
                  --  Clear (V.The_Global_Info.Globals);

                  Phase_1_Info.Insert (Key      => V.The_Global_Info.Name,
                                       New_Item => V.The_Global_Info);

                  for Kind in Tasking_Info_Kind loop
                     if not V.The_Global_Info.Tasking (Kind).Is_Empty then
                        Tasking_Info_Bag (GG_Phase_1, Kind).Insert
                          (V.The_Global_Info.Name,
                           V.The_Global_Info.Tasking (Kind));
                     end if;
                  end loop;

               when EK_Constant_Calls =>
                  declare
                     Const : Name_Graphs.Cursor;
                     --  Position of the caller in the direct calls graph

                     Inserted : Boolean;

                     Call : Name_Lists.Cursor := V.The_Calls.First;

                  begin
                     Constant_Calls.Insert (Key      => V.The_Constant,
                                            Position => Const,
                                            Inserted => Inserted);

                     pragma Assert (Inserted);

                     while Name_Lists.Has_Element (Call) loop
                        Constant_Calls (Const).Insert (V.The_Calls (Call));
                        Name_Lists.Next (Call);
                     end loop;
                  end;

               when EK_Protected_Instance =>
                  declare
                     C : Entity_Name_To_Priorities_Maps.Cursor;
                     --  Position of a list of protected components of a global
                     --  variable and their priorities.

                     Dummy : Boolean;
                     --  Flag that indicates if a key was inserted or if
                     --  it already existed in a map. It is required by
                     --  the hashed-maps API, but not used here.

                  begin
                     --  Find a list of protected components of a global
                     --  variable; if it does not exist then initialize with
                     --  an empty list.
                     Protected_Objects.Insert
                       (Key      => V.The_Variable,
                        Position => C,
                        Inserted => Dummy);

                     Protected_Objects (C).Append (V.The_Priority);
                  end;

               when EK_Task_Instance =>
                  Register_Task_Object (V.The_Type, V.The_Object);

               when EK_Max_Queue_Length =>
                  Max_Queue_Length_Map.Insert
                    (Key      => V.The_Entry,
                     New_Item => V.The_Max_Queue_Length);

               when EK_Direct_Calls =>
                  declare
                     Caller : Name_Graphs.Cursor;
                     --  Position of the caller in the direct calls graph

                     Inserted : Boolean;

                     Callee : Name_Lists.Cursor := V.The_Callees.First;

                  begin
                     Direct_Calls.Insert (Key      => V.The_Caller,
                                          Position => Caller,
                                          Inserted => Inserted);

                     pragma Assert (Inserted);

                     while Name_Lists.Has_Element (Callee) loop
                        Direct_Calls (Caller).Insert (V.The_Callees (Callee));
                        Name_Lists.Next (Callee);
                     end loop;
                  end;

            end case;
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
                     Header : constant String (1 .. 3) := Line (1 .. 3);

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

      GG_State_Constituents := True;

      Note_Time ("gg_read - ALI files read");

      Add_Edges;

      Note_Time ("gg_read - edges added");

      Resolve_Globals : declare

         use type Ada.Containers.Count_Type;

         procedure Debug (Msg : String);
         procedure Dump_Contract (Scop : Entity_Id);
         procedure Dump_Main_Unit_Contracts (Highlight : Entity_Name);
         --  Debug utilities

         procedure Fold (Folded    :        Entity_Name;
                         Contracts :        Entity_Contract_Maps.Map;
                         Patches   : in out Global_Patch_Lists.List)
         with Post => Patches.Length = Patches.Length'Old + 1;
         --  Resolve globals of Folded and append the update to Patches

         procedure Fold_Subtree (Folded    :        Entity_Id;
                                 Contracts :        Entity_Contract_Maps.Map;
                                 Patches   : in out Global_Patch_Lists.List)
         with Post => Patches.Length >= Patches.Length'Old;
         --  Recursively resolve globals of Folded and entities nested in it;
         --  append the update to Patches (??? except for protected type).

         procedure Analyze_Remote_Calls;
         --  Resolve globals of entities from other compilation units, i.e.
         --  subprograms visible by Entity_Id (to have globals for proof) and
         --  packages (to know what is initialized).

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

         --------------------------
         -- Analyze_Remote_Calls --
         --------------------------

         procedure Analyze_Remote_Calls is
            Patches : Global_Patch_Lists.List;

         begin
            for E of Entities_To_Translate loop
               if Ekind (E) in E_Function
                             | E_Procedure
                             | E_Task_Type
                  and then not Is_In_Analyzed_Files (E)
               then
                  declare
                     EN : constant Entity_Name := To_Entity_Name (E);
                  begin
                     if Phase_1_Info.Contains (EN) then
                        Debug ("Fold translated routine " & Unique_Name (E));
                        Fold (Folded    => EN,
                              Contracts => Global_Contracts,
                              Patches   => Patches);
                     end if;
                  end;
               end if;
            end loop;

            --  ??? we only need this for packages with globals that are
            --  mentioned in the contracts which we have just completed.

            for C in Phase_1_Info.Iterate loop
               declare
                  EN : Entity_Name renames Phase_1_Info_Maps.Key (C);
                  Info : Partial_Contract renames
                    Phase_1_Info_Maps.Element (C);
               begin
                  --  ??? remove double call to Find_Entity
                  if Info.Kind = E_Package
                    and then not (Present (Find_Entity (EN))
                                  and then Is_In_Analyzed_Files
                                              (Find_Entity (EN)))
                    and then not Info.Local
                  then
                     Debug ("Fold remote package " & To_String (EN));
                     Fold (Folded    => EN,
                           Contracts => Global_Contracts,
                           Patches   => Patches);
                  end if;
               end;
            end loop;

            --  ??? copy-pasted
            for Patch of Patches loop
               Global_Contracts (Patch.Entity) :=
                 Flow_Names'(Proper      => Patch.Proper,
                             Refined     => Patch.Refined,
                             Initializes => Patch.Initializes,
                             Calls       => <>);
            end loop;

         end Analyze_Remote_Calls;

         -----------
         -- Debug --
         -----------

         procedure Debug (Msg : String) is
         begin
            if XXX then
               Ada.Text_IO.Put_Line (Msg);
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
                        Dump (Indent & "Initializes  ", Contr.Initializes);

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

         ----------
         -- Fold --
         ----------

         procedure Fold (Folded    :        Entity_Name;
                         Contracts :        Entity_Contract_Maps.Map;
                         Patches   : in out Global_Patch_Lists.List)
         is
            Folded_Entity : constant Entity_Id := Find_Entity (Folded);

            Original : Flow_Names renames Contracts (Folded);

            Folded_Scope : constant Flow_Scope :=
              (if Present (Folded_Entity)
               then Get_Flow_Scope (Folded_Entity)
               else Null_Flow_Scope);

            function Callee_Globals
              (Callee : Entity_Name;
               Caller : Entity_Name)
               return Global_Names;

            function Collect (Caller : Entity_Name) return Global_Names;

            function Down_Project
              (Var    : Entity_Name;
               Caller : Entity_Name)
               return Name_Sets.Set;

            function Down_Project
              (Vars   : Name_Sets.Set;
               Caller : Entity_Name)
               return Name_Sets.Set;

            function Down_Project
              (G      : Global_Names;
               Caller : Entity_Name)
               return Global_Names;

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
               if Entity_Contract_Maps.Has_Element (C) then
                  return Down_Project (Contracts (C).Proper, Caller);
               else
                  --  Debug ("Ignoring call to", E);
                  return Global_Names'(others => <>);
               end if;
            end Callee_Globals;

            -------------
            -- Collect --
            -------------

            function Collect (Caller : Entity_Name) return Global_Names is
               Result_Proof_Ins : Name_Sets.Set := Original.Refined.Proof_Ins;
               Result_Inputs    : Name_Sets.Set := Original.Refined.Inputs;
               Result_Outputs   : Name_Sets.Set := Original.Refined.Outputs;
               --  ??? by keeping these separate we don't have to care about
               --  maintaing the Global_Nodes invariant.

               Callees : constant Call_Names :=
                 Categorize_Calls (Caller, Contracts);

            begin
               --  Now collect their globals

               for Callee of Callees.Definite_Calls loop
                  declare
                     G : constant Global_Names :=
                       Callee_Globals (Callee => Callee, Caller => Folded);
                  begin
                     Result_Proof_Ins.Union (G.Proof_Ins);
                     Result_Inputs.Union (G.Inputs);
                     Result_Outputs.Union (G.Outputs);
                  end;
               end loop;

               for Callee of Callees.Proof_Calls loop
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

               for Callee of Callees.Conditional_Calls loop
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

               return (Proof_Ins => Result_Proof_Ins,
                       Inputs    => Result_Inputs,
                       Outputs   => Result_Outputs);
            end Collect;

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
               Var_Scope : constant Entity_Name := Scope (Var);
            begin
               if Scope_Within_Or_Same (Caller, Var_Scope)
                 and then State_Comp_Map.Contains (Var)
               then
                  --  ??? recursive call to Down_Project
                  return State_Comp_Map (Var);
               else
                  return Name_Sets.To_Set (Var);
               end if;
            end Down_Project;

            --  Local_Variables
            Update : Flow_Names;

         --  Start of processing for Fold

         begin
            --  First we resolve globals coming from the globals...
            Update := (Refined => Collect (Folded),
                       others  => <>);

            --  ... and then up-project them as necessary

            Up_Project (Update.Refined, Update.Proper, Folded_Scope);

            pragma Assert (Phase_1_Info.Contains (Folded));

            --  Handle package Initializes aspect
            if Phase_1_Info (Folded).Kind = E_Package then
               declare
                  P : Partial_Contract renames Phase_1_Info (Folded);

                  True_Outputs : constant Name_Sets.Set :=
                    (Update.Proper.Outputs - Update.Proper.Inputs) or
                    Original.Initializes;

                  II : constant Initializes_Info :=
                    (LHS       => True_Outputs and P.Local_Variables,
                     LHS_Proof => True_Outputs and P.Local_Ghost_Variables,
                     RHS       => Update.Proper.Inputs - P.Local_Variables,
                     RHS_Proof => Update.Proper.Proof_Ins -
                                  P.Local_Ghost_Variables);
                  --  The name dependency map for the Folded package
                  --
                  --  LHS and LHS_Proof represent the left hand side of the
                  --  generated initializes aspect. RHS and RHS_Proof
                  --  represent the right hand side of the generated
                  --  Initializes aspect.

               begin
                  --  Invariant: LHS and LHS_Proof are disjoint and do not
                  --  overlap with Initialized_Vars_And_States.
                  Initialized_Vars_And_States.Union (II.LHS);
                  Initialized_Vars_And_States.Union (II.LHS_Proof);

                  Initializes_Aspects.Insert (P.Name, II);
               end;
            end if;

            Patches.Append (Global_Patch'(Entity      => Folded,
                                          Proper      => Update.Proper,
                                          Refined     => Update.Refined,
                                          Initializes => Update.Initializes));
         end Fold;

         ------------------
         -- Fold_Subtree --
         ------------------

         procedure Fold_Subtree (Folded    :        Entity_Id;
                                 Contracts :        Entity_Contract_Maps.Map;
                                 Patches   : in out Global_Patch_Lists.List)
         is
         begin
            for Child of Scope_Map (Folded) loop
               Fold_Subtree (Child, Contracts, Patches);
            end loop;

            if Ekind (Folded) /= E_Protected_Type then
               --  Make sure that we have a mapping from Entity_Name to
               --  Entity_Id. This mapping is typically only registered for
               --  called entities and we need it even if there are no calls.
               Register_Entity (Folded);

               Fold (Folded    => To_Entity_Name (Folded),
                     Contracts => Contracts,
                     Patches   => Patches);
            end if;
         end Fold_Subtree;

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

            --  ??? this could go into Common_Containers; in particular,
            --  To_List has a body here, because it is needed to elaborate
            --  a constant.

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
            --  A singleton containers a special value that represents a
            --  dependency on a variable input. (By having a special-value
            --  with the same type as non-variable dependencies we adoid
            --  discriminated records, which would be just too verbose.)

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
               return Name_Lists.List;
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

                  return Inputs;

                  --  ??? calls to Pick_Constants repeat iterations done by
                  --  Has_Variables, but this stays in the same complexity
                  --  class and makes the code shorter.
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
                     else Direct_Inputs_Of_Subprogram (E));

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
               Patches : Global_Patch_Lists.List;

            begin
               Fold_Subtree (Folded    => Root_Entity,
                             Contracts => Global_Contracts,
                             Patches   => Patches);

               for Patch of Patches loop
                  Global_Contracts (Patch.Entity) :=
                    Flow_Names'(Proper      => Patch.Proper,
                                Refined     => Patch.Refined,
                                Initializes => Patch.Initializes,
                                Calls       => <>);
               end loop;

               --  Only debug output from now on
               Debug_Traversal (Root_Entity);

               Dump_Main_Unit_Contracts
                 (Highlight => To_Entity_Name (Root_Entity));
            end;

            Analyze_Remote_Calls;

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
      --  True. Notice that we set GG_Generated to True before we remove edges
      --  leading to constants without variable input. The reasoning behind
      --  this is to use the generated globals instead of the computed globals
      --  when we call Get_Globals from within Has_Variable_Input.
      GG_Generated := True;

      --  Now that the globals are generated, we use them to also generate the
      --  initializes aspects.
      Print_Generated_Initializes_Aspects;

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
      --  Vertex V might be null if we only have a spec for entity Ent
      if V /= Null_Vertex then
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

   function Get_Constituents (E : Entity_Name) return Name_Sets.Set
   is (State_Comp_Map (E));

   ----------------------------
   -- GG_Encapsulating_State --
   ----------------------------

   function GG_Encapsulating_State (EN : Entity_Name) return Any_Entity_Name is
      C : constant Name_Maps.Cursor := Comp_State_Map.Find (EN);
      use Name_Maps;
   begin
      return (if Has_Element (C)
              then Element (C)
              else Null_Entity_Name);
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
     (Initialized_Vars_And_States.Contains (EN)
        or else GG_Has_Async_Writers (EN));

   --------------------
   -- GG_Is_Volatile --
   --------------------

   function GG_Is_Volatile (EN : Entity_Name) return Boolean
     renames Volatile_Vars.Contains;

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
               if Is_Predefined (Callee) then
                  --  All user-defined callers of predefined potentially
                  --  blocking subprograms have been already marked as
                  --  potentially blocking, so here we can safely assume
                  --  that any call to predefined subprogram is nonblocking.
                  null;
               else
                  if not Phase_1_Info (Callee).Nonblocking then
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
      return (not Phase_1_Info (EN).Nonblocking)
        or else Calls_Potentially_Blocking_Subprogram;
   end Is_Potentially_Blocking;

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

   -----------------------------------------
   -- Print_Generated_Initializes_Aspects --
   -----------------------------------------

   procedure Print_Generated_Initializes_Aspects is
   begin
      if Debug_Print_Generated_Initializes then
         Write_Line ("Synthesized initializes aspects:");
         for Init in Initializes_Aspects.Iterate loop
            declare
               Pkg : Entity_Name renames Initializes_Aspects_Maps.Key (Init);
               II  : Initializes_Info renames Initializes_Aspects (Init);

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
      end if;
   end Print_Generated_Initializes_Aspects;

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

   -----------
   -- Scope --
   -----------

   function Scope (EN : Entity_Name) return Entity_Name is

      use Ada.Strings;
      use Ada.Strings.Fixed;

      S : constant String := To_String (EN);
      J : constant Natural := Index (Source  => S,
                                     Pattern => "__",
                                     From    => S'Last,
                                     Going   => Backward);
      --  ??? This is hackish, I know! The alternative is to try with
      --  Find_Entity or to record hierarchy in the ALI file.

   begin
      return To_Entity_Name (S (S'First .. J - 1));
   end Scope;

   --------------------------
   -- Scope_Within_Or_Same --
   --------------------------

   function Scope_Within_Or_Same (Scope1, Scope2 : Entity_Name)
                                  return Boolean
   is
      Scope1_Str : constant String := To_String (Scope1);
      Scope2_Str : constant String := To_String (Scope2);

   begin
      return
        Scope1_Str'Length >= Scope2_Str'Length
        and then
          Scope1_Str
            (Scope2_Str'First ..
               Scope2_Str'First + Scope2_Str'Length - 1) =
          Scope2_Str;
   end Scope_Within_Or_Same;

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

      --  Local variables:
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
        Get_Name_String (Chars (Main_Unit_Entity)) & "_constants_2";

   --  Start of processing for Print_Graph

   begin
      if Gnat2Why_Args.Flow_Advanced_Debug then
         G.Write_Pdf_File
           (Filename  => Filename,
            Node_Info => NDI'Access,
            Edge_Info => EDI'Access);
      end if;
   end Print;

end Flow_Generated_Globals.Phase_2;
