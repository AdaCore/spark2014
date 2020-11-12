------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--        F L O W . G E N E R A T E D _ G L O B A L S . P A R T I A L       --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                Copyright (C) 2016-2020, Altran UK Limited                --
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

with Ada.Strings.Unbounded;            use Ada.Strings.Unbounded;
with Ada.Containers.Doubly_Linked_Lists;
with Ada.Containers.Hashed_Maps;
with Ada.Text_IO;                      use Ada.Text_IO;
with Common_Iterators;                 use Common_Iterators;
with Flow.Dynamic_Memory;              use Flow.Dynamic_Memory;
with Flow_Dependency_Maps;             use Flow_Dependency_Maps;
with Flow_Generated_Globals.Traversal; use Flow_Generated_Globals.Traversal;
with Flow_Generated_Globals.Phase_1;   use Flow_Generated_Globals.Phase_1;
with Flow_Refinement;                  use Flow_Refinement;
with Flow.Slice;                       use Flow.Slice;
with Flow_Utility;                     use Flow_Utility;
with Flow_Visibility;                  use Flow_Visibility;
with Gnat2Why_Args;                    use Gnat2Why_Args;
with Graphs;
with Lib;                              use Lib;
with Opt;                              use Opt;
with Sem_Aux;                          use Sem_Aux;
with Sem_Prag;                         use Sem_Prag;
with Sem_Type;                         use Sem_Type;
with Sem_Util;                         use Sem_Util;
with Sinfo;                            use Sinfo;
with Snames;                           use Snames;
with SPARK_Definition;                 use SPARK_Definition;
with SPARK_Definition.Annotate;        use SPARK_Definition.Annotate;
with SPARK_Frame_Conditions;           use SPARK_Frame_Conditions;
with SPARK_Util.Subprograms;           use SPARK_Util.Subprograms;
with SPARK_Xrefs;                      use SPARK_Xrefs;
with Why;

package body Flow_Generated_Globals.Partial is

   use type Node_Sets.Set;
   use type Node_Lists.List;
   use type Ada.Containers.Count_Type;
   --  for the "=" and "or" operators

   ----------------------------------------------------------------------------
   --  Debugging
   ----------------------------------------------------------------------------

   Indent : constant String := "  ";
   --  ??? use indent/outdent facilities from Output (requires writing some
   --  wrappers about ANSI color strings)

   ----------------------------------------------------------------------------
   --  Utilities for constants with variable input
   ----------------------------------------------------------------------------

   Variable_Input : constant Entity_Id := Empty;
   --  Represents dependency on a variable input. It is chosen to not collide
   --  with other entities represented in graphs from the Constant_Graphs
   --  package.

   function To_List (E : Entity_Id) return Node_Lists.List
   with Post => To_List'Result.Length = 1
                  and then
                To_List'Result.First_Element = E;
   --  Returns a singleton list with E

   --  ??? this could go into Common_Containers; in particular, To_List has
   --  a body here, because it is needed to elaborate a constant.

   -------------
   -- To_List --
   -------------

   function To_List (E : Entity_Id) return Node_Lists.List is
      Singleton : Node_Lists.List;
   begin
      Singleton.Append (E);
      return Singleton;
   end To_List;

   Variable : constant Node_Lists.List := To_List (Variable_Input);
   --  A singleton containers a special value that represents a dependency
   --  on a variable input. (By having a special-value with the same type as
   --  non-variable dependencies we adoid discriminated records, which would
   --  be just too verbose.)

   ----------------------------------------------------------------------------
   --  Preliminaries
   ----------------------------------------------------------------------------

   function Is_Caller_Entity (E : Entity_Id) return Boolean with Ghost;
   --  Returns True iff E represent an entity is can call other routines

   function Is_Callable (E : Entity_Id) return Boolean;
   --  Returns True iff E might be called

   function Scope_Truly_Within_Or_Same
     (Inner, Outer : Entity_Id) return Boolean
   is
     (Is_In_Analyzed_Files (Inner)
      and then Scope_Within_Or_Same (Inner, Outer))
   with Pre => Is_In_Analyzed_Files (Outer);
   --  Determines if entity E is the same as Analyzed or is "truly" within,
   --  i.e. in the same compilation unit as Analyzed and inside Analyzed. (It
   --  differs from Scope_Within_Or_Same for entities in child units). This
   --  routine is only intented to detect entities belonging to scopes of the
   --  current compilation unit (hence the Pre).

   ----------------------
   -- Is_Caller_Entity --
   ----------------------

   function Is_Caller_Entity (E : Entity_Id) return Boolean is
     (Ekind (E) in Flow_Generated_Globals.Traversal.Container_Scope);
   --  ??? Container_Scope isn't the best name; rethink
   --  ??? not sure how Protected_Type fits here

   ----------------------------------------------------------------------------
   --  Types
   ----------------------------------------------------------------------------

   type No_Colours is (Dummy_Color);
   --  Dummy type inhabited by only a single value (just like a unit type in
   --  OCaml); needed for graphs with colorless edges.

   --  ### Idea: Lets try to use tri-valued logic instead of using
   --  boolean constant Meaningless

   type Contract is record
      Globals : Flow_Nodes;

      Direct_Calls : Node_Sets.Set;  --   ??? Callee_Set
      --  For compatibility with old GG (e.g. assumptions)
      --
      --  ### All the direct calls; this is what we need for the
      --  non-global contract synthesis (for example
      --  nonblocking). This is always a superset Calls in Globals
      --  (except for a front-end bug w.r.t. calls in contracts)
      --
      --  ### What is the TN for this?

      Local_Variables : Global_Set;

      --  ### Intention for these is to only capture the obvious (for
      --  example, has loop at end, aspect no_return, etc.). This is
      --  what feeds into the closure/fold in phase 2 to actually work
      --  out what is going on.

      Has_Terminate    : Boolean;
      Has_Subp_Variant : Boolean;
      --  Only meaningful for subprograms and entries

      Nonreturning       : Boolean;
      Nonblocking        : Boolean;
      Entry_Calls        : Entry_Call_Sets.Set;
      Tasking            : Tasking_Info;
      Calls_Current_Task : Boolean;
      --  Only meaningfull only for entries, functions and procedures and
      --  initially for packages (nested in entries, functions or procedures).
      --
      --  Only recorded to the ALI files for entries, functions and procedures
   end record;
   --  ### This record contains all the contracts we generate and is
   --  _fully_ populated by Do_Global.

   package Entity_Contract_Maps is new Ada.Containers.Hashed_Maps
     (Key_Type        => Entity_Id,  --  ??? some Checked_Entity_Id
      Element_Type    => Contract,
      Hash            => Node_Hash,
      Equivalent_Keys => "=");
   --  Containers with contracts generated based on the current compilation
   --  unit alone.

   type Global_Patch is record
      Entity  : Entity_Id;
      Globals : Flow_Nodes;
   end record;

   package Global_Patch_Lists is new Ada.Containers.Doubly_Linked_Lists
     (Element_Type => Global_Patch);

   package Constant_Graphs is new Graphs
     (Vertex_Key   => Entity_Id,
      Key_Hash     => Node_Hash,
      Edge_Colours => No_Colours,
      Null_Key     => Entity_Id'Last,
      Test_Key     => "=");
   --  Graphs for resolving constants without variable input within the current
   --  compilation unit.
   --
   --  Vertices represent:
   --  * constants with possibly variable inputs,
   --  * subprograms called (directly or indirectly) from constants'
   --    initilization expressions,
   --  * a hardcoded key, which represents a dependency on a variable input.
   --
   --  Edges represent dependencies constants' initialization.

   Meaningless : constant Boolean := False;
   --  Meaningless value needed to silence checks for invalid data

   ----------------------------------------------------------------------------
   --  Specs
   ----------------------------------------------------------------------------

   function Preanalyze_Body (E : Entity_Id) return Contract;
   --  Direct contract based on the analysis of E, when body is available

   function Preanalyze_Spec (E : Entity_Id) return Contract
   with Pre => (if Entity_In_SPARK (E)
                then not Entity_Body_In_SPARK (E));
   --  Direct contract based on the analysis of E, when only spec is available

   function Categorize_Calls
     (E         : Entity_Id;
      Analyzed  : Entity_Id;
      Contracts : Entity_Contract_Maps.Map)
   return Call_Nodes
   with Pre => Is_Caller_Entity (E) and then
               Scope_Truly_Within_Or_Same (E, Analyzed);
   --  Categorize calls from E to entities nested within Analyzed into Proof,
   --  Conditional and Definite calls.
   --
   --  ### We work out all the (transitive) calls for E, BUT we do not
   --  go outside the subtree rooted at Analyzed. Calls to such
   --  subprograms are included as is and do not contribute to the
   --  closure.

   function Contract_Calls (E : Entity_Id) return Node_Sets.Set
   with Pre => Ekind (E) in Entry_Kind
                          | E_Function
                          | E_Procedure,
        Post => (for all Call of Contract_Calls'Result =>
                    Ekind (Call) in E_Function | E_Subprogram_Type);
   --  Return direct calls in the contract of E, i.e. in its Pre, Post and
   --  Contract_Cases.

   function Contract_Globals
     (E       : Entity_Id;
      Refined : Boolean)
      return Global_Nodes;
   --  Return globals from the Global and Depends contracts of E (or from their
   --  refined variants iff Refined is True).

   procedure Debug (Label : String; E : Entity_Id);
   --  Display Label followed by the entity name of E

   procedure Do_Global
     (Analyzed  :        Entity_Id;
      Contracts : in out Entity_Contract_Maps.Map)
   with Pre => Is_Caller_Entity (Analyzed);
   --  ### Overview
   --
   --  Consider a structure like this:
   --     Pkg
   --       \ Proc_1
   --              \ Proc_2
   --              \ Proc_3
   --
   --  We process bottom up (via recursion), so first look at
   --  Do_Global of Proc_2, then Proc_3, then Proc_1 and finally
   --  Pkg. On each step we call Fold on ourself (and everything
   --  underneath), except for leafs since Fold here would be an
   --  identity function.
   --
   --  Note we have a similar approach in Phase_2 via Fold_Subtree and
   --  Fold; except that we also consider other compilation
   --  units. Here in Phase_1 we only look at the current compilation
   --  unit.
   --
   --  Analyzed - the containing scope we currently look at.
   --
   --  Contracts - this is where we put things; in general we put
   --  something at Contracts (Analyzed) except in a few cases, and we
   --  don't modify any other mappings directly (indirectly via
   --  recursive calls to Do_Global).

   procedure Do_Preanalysis
     (Contracts : in out Entity_Contract_Maps.Map);
   --  ### This is actually the first thing we do (before any call to
   --  Do_Global). We call Preanalyze_Spec or _Body for all entities
   --  we will ultimately analyze and place initial mappings into
   --  Contracts.
   --
   --  These will then be fine-tuned (i.e. we take care of
   --  abstraction) in Do_Global.

   --  Collect contracts on the intraprocedural analysis alone

   procedure Dump (Contracts : Entity_Contract_Maps.Map; Analyzed : Entity_Id);
   --  Display contracts highlighing the analyzed entity

   procedure Filter_Local (E : Entity_Id; Nodes : in out Node_Sets.Set)
   with Post => Nodes.Is_Subset (Of_Set => Nodes'Old);
   --  Remove those Nodes which are declared inside E

   procedure Filter_Local (E : Entity_Id; G : in out Global_Nodes);
   --  Same as above, lifted to container with Proof_In/Input/Output globals

   procedure Fold (Folded    :        Entity_Id;
                   Analyzed  :        Entity_Id;
                   Contracts :        Entity_Contract_Maps.Map;
                   Patches   : in out Global_Patch_Lists.List);
   --  Main workhorse for the partial generated globals
   --
   --  ### As we call Fold from Do_Global, initially Folded and
   --  Analyzed are the same. As we recurse down, Folded keeps track
   --  of where we are, but Analyzed never changes. We look at
   --  Contracts and produce patches (after Fold returns there will be
   --  a patch for Folded -> Contracts in the Patches list) [except in
   --  a few cases where we don't do anything].
   --
   --  As Do_Global goes up the tree, we call Fold which makes things
   --  more abstract.

   function Frontend_Calls (E : Entity_Id) return Node_Sets.Set;
   --  Return direct calls using the frontend cross-references

   function Frontend_Globals (E : Entity_Id) return Global_Nodes;
   --  Return globals using the frontend cross-references

   function Is_Empty (G : Global_Nodes) return Boolean;
   --  Return True iff all components of the G are empty

   procedure Print (G : Constant_Graphs.Graph);
   --  Print graph with dependencies between constants with variable input

   procedure Resolve_Constants
     (Contracts      :     Entity_Contract_Maps.Map;
      Constant_Graph : out Constant_Graphs.Graph);
   --  Create a graph rooted at constants in Globals of subprogram from the
   --  current compilation unit. This code has very much in common with code
   --  for potentially blocking, termination, etc. ??? most likely this could
   --  be somehow refactored.

   function Resolved_Inputs
     (E              : Entity_Id;
      Constant_Graph : Constant_Graphs.Graph)
      return Node_Lists.List
   with Pre  => Ekind (E) = E_Constant,
        Post => (Resolved_Inputs'Result = Variable
                  or else
                (for all E of Resolved_Inputs'Result =>
                   Ekind (E) in E_Function | E_Procedure
                     and then
                   not Is_In_Analyzed_Files (E)));
   --  Returns either a singleton list representing a variable input or a
   --  list with subprograms from other compilation unit called (directly
   --  or indirectly) in the initialization of E.

   procedure Strip_Constants
     (From           : in out Flow_Nodes;
      Constant_Graph :        Constant_Graphs.Graph);
   --  Filter constants without variable from contract

   procedure Write_Constants_To_ALI (Constant_Graph : Constant_Graphs.Graph);
   --  Register calls from the initial expressions of Locals to subprograms in
   --  other compilation units.

   procedure Write_Contracts_To_ALI
     (E              :        Entity_Id;
      Constant_Graph :        Constant_Graphs.Graph;
      Contracts      : in out Entity_Contract_Maps.Map)
   with Pre => Is_Caller_Entity (E);
   --  Strip constants from contract and write in to the ALI writer (probably
   --  should write it directly).

   ----------------------------------------------------------------------------
   --  Bodies
   ----------------------------------------------------------------------------

   ---------------------
   -- Preanalyze_Body --
   ---------------------

   function Preanalyze_Body (E : Entity_Id) return Contract
   is
      FA : constant Flow_Analysis_Graphs :=
        Flow_Analyse_Entity (E, Generating_Globals => True);

      Contr : Contract;

   begin
      --  ??? I do not understand what Is_Generative means
      if FA.Is_Generative then
         Compute_Globals
           (FA,
            Globals               => Contr.Globals.Refined,
            Proof_Calls           => Contr.Globals.Calls.Proof_Calls,
            Definite_Calls        => Contr.Globals.Calls.Definite_Calls,
            Conditional_Calls     => Contr.Globals.Calls.Conditional_Calls,
            Local_Definite_Writes => Contr.Globals.Initializes.Refined);

         Contr.Local_Variables := FA.GG.Local_Variables;

      else
         case Ekind (E) is
            when Entry_Kind
               | E_Function
               | E_Procedure
               | E_Task_Type
            =>
               --  Use globals from spec, but calls and tasking info from body
               Contr.Globals.Proper  := Contract_Globals (E, Refined => False);
               Contr.Globals.Refined := Contract_Globals (E, Refined => True);

            when E_Package =>

               --  We want to store objects from the LHSs of explicit
               --  Initializes contracts in the ALI file to know that are
               --  claimed to be initialized even if they are only known by
               --  Entity_Name.

               for Clause in Parse_Initializes (E, Get_Flow_Scope (E)).Iterate
               loop
                  declare
                     LHS : constant Entity_Id :=
                       Get_Direct_Mapping_Id (Dependency_Maps.Key (Clause));

                  begin
                     --  Ignore constants without variable inputs, because they
                     --  would violate a type predicate on generated contract
                     --  before being stripped from there.

                     if Ekind (LHS) /= E_Constant
                       or else Has_Variable_Input (LHS)
                     then
                        Contr.Globals.Initializes.Proper.Insert (LHS);
                     end if;
                  end;
               end loop;

            when E_Protected_Type =>
               null; --  ??? do nothing for now

            when others =>
               raise Program_Error;
         end case;
      end if;

      --  Register direct calls without splitting them into proof, definite
      --  and conditional; this is necessary because calls to subprograms with
      --  user-written Global or Depends contracts are resolved inline and do
      --  not appear in proof, definite or conditional.
      --  ??? not sure about protected types
      if Ekind (E) /= E_Protected_Type then

         --  Ignore calls via access-to-subprogram, because we can't know the
         --  actual subprogram and thus we assume it to be pure.

         for Call of FA.Direct_Calls loop
            if Ekind (Call) /= E_Subprogram_Type then
               Contr.Direct_Calls.Insert (Call);
            end if;
         end loop;
      end if;

      --  Register abstract state components for packages whose body has
      --  SPARK_Mode => On or None.
      if Ekind (E) = E_Package
        and then Has_Non_Null_Abstract_State (E)
        and then Present (Body_Entity (E))
        and then
          (No (SPARK_Pragma (Body_Entity (E)))
             or else
           Get_SPARK_Mode_From_Annotation
             (SPARK_Pragma (Body_Entity (E))) = Opt.On)
      then
         GG_Register_State_Refinement (E);
      end if;

      --  We register the following:
      --  * subprograms which contain at least one loop that may not terminate
      --  * procedures annotated with No_Return
      --  * subprograms which call predefined procedures with No_Return
      --  * subprograms with calls via access-to-subprogram

      --  ??? This flag is only meaningful for functions, procedures, entries
      --  and non-library-level packages, but meaningless for tasks and
      --  library-level packages, which cannot be called from the outside.
      Contr.Nonreturning :=
        (FA.Kind = Kind_Subprogram
          or else
         (FA.Kind = Kind_Package
          and then Entity_Body_In_SPARK (FA.Spec_Entity)))
          and then
        (FA.Has_Potentially_Nonterminating_Loops
           or else
         No_Return (E)
           or else
         (for some Callee of FA.Direct_Calls =>
             Ekind (Callee) = E_Subprogram_Type
               or else
             (In_Predefined_Unit (Callee) and then No_Return (Callee))));

      --  Check for potentially blocking statements in bodies of callable
      --  entities, i.e. entries and subprograms. Specs never contain any
      --  statements.

      Contr.Nonblocking :=
        (if Is_Callee (E)
         then FA.Has_Only_Nonblocking_Statements
         else Meaningless);

      --  Deal with tasking-related stuff
      Contr.Tasking     := FA.Tasking;
      Contr.Entry_Calls := FA.Entries;

      return Contr;
   end Preanalyze_Body;

   ---------------------
   -- Preanalyze_Spec --
   ---------------------

   function Preanalyze_Spec (E : Entity_Id) return Contract is

      Contr : Contract;

      function Unsynchronized_Globals (G : Global_Nodes) return Node_Sets.Set;
      --  Returns unsynchronized globals from G

      function Has_No_Body_Yet (E : Entity_Id) return Boolean is
        (Ekind (E) in E_Function | E_Procedure
         and then No (Subprogram_Body_Entity (E)));
      --  Returns True if subprogram E does not have a body yet (no .adb)

      ----------------------------
      -- Unsynchronized_Globals --
      ----------------------------

      function Unsynchronized_Globals (G : Global_Nodes) return Node_Sets.Set
      is
         Unsynch : Node_Sets.Set;

         procedure Collect_Unsynchronized (Vars : Node_Sets.Set);

         ----------------------------
         -- Collect_Unsynchronized --
         ----------------------------

         procedure Collect_Unsynchronized (Vars : Node_Sets.Set) is
         begin
            for E of Vars loop
               if not (Is_Heap_Variable (E) or else Is_Synchronized (E)) then
                  Unsynch.Include (E);
               end if;
            end loop;
         end Collect_Unsynchronized;

      --  Start of processing for Unsynchronized_Globals

      begin
         Collect_Unsynchronized (G.Proof_Ins);
         Collect_Unsynchronized (G.Inputs);
         Collect_Unsynchronized (G.Outputs);

         return Unsynch;
      end Unsynchronized_Globals;

   --  Start of processing for Preanalyze_Spec

   begin
      -------------------------------------------------------------------------
      --  Properties related to Global and Refined_Global contracts (and
      --  accesses to unsynchronized variables, which follows from them).
      -------------------------------------------------------------------------
      --
      --  For entities with explicit Global and mixed SPARK_Mode (i.e.
      --  SPARK_Mode => On on spec and SPARK_Mode => Off on body) we pick the
      --  Global contract as it is and leave the conditional/definite/proof
      --  calls as empty (so that no extra globals will come from these calls).
      --  This behaviour is mandated by the spirit of respecting contracts at
      --  the SPARK_Mode On/Off boundary.
      --
      --  For entities with explicit Global and entirely not in SPARK (i.e.
      --  SPARK_Mode => Off on both spec and body) we do the same both to keep
      --  things simple and to give users some control over the often
      --  unreliable approximation based on the frontend cross-references.

      if Ekind (E) in Entry_Kind
                    | E_Function
                    | E_Procedure
                    | E_Task_Type
      then
         if Has_User_Supplied_Globals (E) then

            Contr.Globals.Proper := Contract_Globals (E, Refined => False);

            --  ??? not sure what happens about refined globals

            Contr.Tasking (Unsynch_Accesses) :=
              Unsynchronized_Globals (Contr.Globals.Proper);

         --  Capture (Yannick's) "frontend globals"; once they will end up in
         --  the ALI file they should be indistinguishable from other globals.

         else
            Contr.Globals.Refined := Frontend_Globals (E);

            --  Frontend globals does not distinguish Proof_Ins from Inputs;
            --  conservatively assume that all reads belong to Inputs.
            pragma Assert (Contr.Globals.Refined.Proof_Ins.Is_Empty);

            Contr.Tasking (Unsynch_Accesses) :=
              Unsynchronized_Globals (Contr.Globals.Refined);

            Contr.Globals.Calls.Conditional_Calls := Frontend_Calls (E);
         end if;
      end if;

      -------------------------------------------------------------------------
      --  Other properties, not related to globals
      -------------------------------------------------------------------------

      if Entity_In_SPARK (E) then
         if Is_Callable (E) then

            --  Ignore calls via access-to-subprogram, because we can't know
            --  the actual subprogram and thus we assume it to be pure.

            for Call of Contract_Calls (E) loop
               if Ekind (Call) /= E_Subprogram_Type then
                  Contr.Direct_Calls.Insert (Call);
               end if;
            end loop;
         end if;

         --  For subprograms in a generic predefined unit with its body not
         --  in SPARK, we also register actual subprogram parameters of its
         --  instantiation, except for predefined arithmetic operators, because
         --  they are irrelevant.
         if Ekind (E) in E_Function | E_Procedure
           and then In_Predefined_Unit (E)
         then
            declare
               Enclosing_Instance : Entity_Id := E;

            begin
               loop
                  Enclosing_Instance :=
                    Enclosing_Generic_Instance (Enclosing_Instance);

                  if Present (Enclosing_Instance) then
                     for S of Generic_Actual_Subprograms (Enclosing_Instance)
                     loop
                        case Ekind (S) is
                           when E_Function | E_Procedure =>
                              Contr.Direct_Calls.Include (S);

                           when E_Operator =>
                              pragma Assert (In_Predefined_Unit (S));

                           when others =>
                              raise Program_Error;
                        end case;
                     end loop;
                  else
                     exit;
                  end if;
               end loop;
            end;
         end if;

         --  We register subprograms with their body not in SPARK as
         --  nonreturning except when they are:
         --  * predefined (or are instances of predefined subprograms)
         --  * imported
         --  * intrinsic
         --  * have no body yet (no .adb) and are not procedures annotated with
         --    No_Return.

         Contr.Nonreturning := not
           (In_Predefined_Unit (E)
              or else
            Is_Imported (E)
              or else
            Is_Intrinsic (E)
              or else
            (Has_No_Body_Yet (E) and then not No_Return (E)));

         --  For library-level packages and protected-types the non-blocking
         --  status is meaningless. Otherwise, it is either a user instance of
         --  a predefined unit for which we generate contracts but it is the
         --  Ada RM that decides is its blocking status; or we conservatively
         --  assume it to be potentially blocking.

         Contr.Nonblocking :=
           (if Is_Callee (E)
            then (if In_Predefined_Unit (E)
                  then not Is_Predefined_Potentially_Blocking (E)
                  else False)
            else Meaningless);

         --  In a contract it is syntactically not allowed to suspend on a
         --  suspension object, call a protected procedure or entry, and it is
         --  semantically not allowed to externally call a protected function
         --  (because such calls are volatile and they would occur in an
         --  interfering context).
         pragma Assert (Contr.Tasking (Suspends_On).Is_Empty);
         pragma Assert (Contr.Tasking (Locks).Is_Empty);
         pragma Assert (Contr.Entry_Calls.Is_Empty);

      --  Otherwise, fill in dummy values

      else
         pragma Assert (Contr.Direct_Calls.Is_Empty);

         Contr.Nonreturning := Meaningless;
         Contr.Nonblocking  := Meaningless;
      end if;

      return Contr;
   end Preanalyze_Spec;

   ----------------------
   -- Categorize_Calls --
   ----------------------

   function Categorize_Calls
     (E         : Entity_Id;
      Analyzed  : Entity_Id;
      Contracts : Entity_Contract_Maps.Map)
      return Call_Nodes
   is
      Original : Call_Nodes renames Contracts (E).Globals.Calls;

      --  Categorization is done in two steps: first, we find subprograms
      --  called definitely, conditionally and in proof contexts and not care
      --  about overlapping (e.g a routine that is called both definitely and
      --  in proof will be found twice); then we handle overlapping, which is
      --  enforced by the Call_Nodes type predicate. The first step is
      --  difficult, then overlapping is simple.
      --
      --  The first step is relatively easy to specify inductively, but its
      --  imperative implementation is quite hard to follow. Verifying it would
      --  be very reassuring. So here is a spec, and verification is left as an
      --  exercise for the reader.
      --
      --  Notation
      --  ========
      --
      --  Def, Cond and Proof denote sets of subprograms called definitely,
      --  conditionally and in proof contexts (they might overlap),
      --  respectively. That's what we are looking for.
      --
      --  Def_i, Cond_i and Proof_i denote sets of subprograms called
      --  "immediately", e.g. those whose calls appear in the CFG of the
      --  caller. That's what we get in Contracts.
      --
      --  Both the prefixed and unprefixed sets are represented as relations
      --  and typed in the curried style typical to proof assistants, e.g.:
      --  "Def x y" reads as "x will definitely call y" (either immediately or
      --  as an effect of a call to some other subprogram, which we typically
      --  call "p" for proxy).
      --
      --  Logical symbols are typed in the style of HOL proof assistant, i.e.
      --  a \/ b  = "a or b"
      --  a /\ b  = "a and b"
      --  ?x. F x = "exists x such that F x"
      --
      --  Specification
      --  =============
      --
      --  Subprograms called definitely are inductively specified as:
      --
      --  Def x y =
      --    Def_i x y \/
      --    ?p. Def x p /\ Def_i p y,
      --
      --  i.e. they are either immediately (and definitely) called from x or
      --  immediately called from some of its definite callees. In other words,
      --  they are reachable from x through a chain of definitely called
      --  subprograms.
      --
      --  Subprograms called conditionally are more complicated:
      --
      --  Cond x y =
      --    Cond_i x y \/
      --    (?p. Cond x p /\ (Def_i p y \/ Cond_i p y)) \/
      --    (?p. Def x p /\ Cond_i p y),
      --
      --  i.e. they are either immediately (and conditionally) called from x,
      --  immediately called (conditionally or definitely) from one of its
      --  conditional callees, or immediately (but conditionally) called from
      --  one of its definite callees. Note: this definition uses Def from the
      --  previous one.
      --
      --  And those called in proof context are the most complicated:
      --
      --  Proof x y =
      --    Proof_i x y \/
      --    (?p. (Def x p \/ Cond x p) /\ Proof_i p y) \/
      --    (?p. Proof x p /\ (Def_i p y \/ Cond_i p y \/ Proof_i p y)),
      --
      --  i.e. they are either immediately called from x in a proof context, or
      --  are immediately called from a conditional or definitive callee of x
      --  in a proof context, or are immediately called no matter how from a
      --  proof callee of x. Note: this definitions uses Def and Cond from the
      --  previous ones.

      O_Proof, O_Conditional, O_Definite : Node_Sets.Set;
      --  Sets for intermediate results, i.e. overlapping sets of calls

      procedure Crash_On_Abstract_Callee (Pick : Entity_Id)
      with Pre => Is_Overloadable (Pick) or else Ekind (Pick) = E_Package;
      --  ??? global generation with calls to abstract subprograms is not
      --  yet implemented; explicitly crash with an informational message,
      --  as otherwise we would crash with "key not in map" when accessing
      --  "Contracts (Pick)".

      ------------------------------
      -- Crash_On_Abstract_Callee --
      ------------------------------

      procedure Crash_On_Abstract_Callee (Pick : Entity_Id) is
      begin
         if Is_Overloadable (Pick) and then Is_Abstract_Subprogram (Pick) then
            Ada.Text_IO.Put_Line
              ("[Categorize_Calls] call to abstract subprogram = "
               & Full_Source_Name (E) & " -> " & Full_Source_Name (Pick));
            raise Why.Not_Implemented;
         end if;
      end Crash_On_Abstract_Callee;

   --  Start of processing for Categorize_Calls

   begin
      --  Definitive calls are the easiest to find and the implementation is
      --  fairly straightforward, as it ignores conditional and proof calls.
      --  Note: this could be done with a simple closure of a graph with only
      --  definitive calls, but we would still need a similar traversal to
      --  populate such a graph.
      --
      --  We maintain two sets: Todo, initialized according to the base case of
      --  the inductive specification; and Done, processed according to the
      --  inductive cases. For definitive calls those two sets are enough; for
      --  conditional and proof calls they are split into subsets for handling
      --  different inductive cases.

      Find_Definite_Calls : declare
         Todo : Node_Sets.Set := Original.Definite_Calls;
         Done : Node_Sets.Set;

      begin
         loop
            if not Todo.Is_Empty then
               declare
                  Pick : constant Entity_Id := Todo.First_Element;

               begin
                  Done.Insert (Pick);

                  if Scope_Truly_Within_Or_Same (Pick, Analyzed) then

                     Crash_On_Abstract_Callee (Pick);

                     Todo.Union
                       (Contracts (Pick).Globals.Calls.Definite_Calls - Done);
                  end if;

                  Todo.Delete (Pick);
               end;
            else
               exit;
            end if;
         end loop;

         pragma Assert (Original.Definite_Calls.Is_Subset (Of_Set => Done));

         Node_Sets.Move (Target => O_Definite,
                         Source => Done);
      end Find_Definite_Calls;

      --  Conditional calls are more difficult to find, but the implementation
      --  is still similar to the previous one. It maintains two sets of called
      --  subprograms: those called definitively and those called
      --  conditionally.

      Find_Conditional_Calls : declare
         type Calls is record
            Conditional, Definite : Node_Sets.Set;
         end record;

         Todo : Calls := (Conditional => Original.Conditional_Calls,
                          Definite    => Original.Definite_Calls);

         Done : Calls;

      begin
         loop
            if not Todo.Conditional.Is_Empty then
               declare
                  Pick : constant Entity_Id := Todo.Conditional.First_Element;

               begin
                  Done.Conditional.Insert (Pick);

                  if Scope_Truly_Within_Or_Same (Pick, Analyzed) then

                     Crash_On_Abstract_Callee (Pick);

                     declare
                        Picked : Call_Nodes renames
                          Contracts (Pick).Globals.Calls;

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
                  Pick : constant Entity_Id := Todo.Definite.First_Element;

               begin
                  Done.Definite.Insert (Pick);

                  if Scope_Truly_Within_Or_Same (Pick, Analyzed) then

                     Crash_On_Abstract_Callee (Pick);

                     declare
                        Picked : Call_Nodes renames
                          Contracts (Pick).Globals.Calls;

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

         Node_Sets.Move (Target => O_Conditional,
                         Source => Done.Conditional);
      end Find_Conditional_Calls;

      --  Proof calls turns out to be not really harder than conditional calls;
      --  their implementation follows the very same pattern.

      Find_Proof_Calls : declare
         type Calls is record
            Proof, Other : Node_Sets.Set;
         end record;

         Todo : Calls := (Proof => Original.Proof_Calls,
                          Other => Original.Conditional_Calls or
                                   Original.Definite_Calls);

         Done : Calls;

      begin
         loop
            if not Todo.Proof.Is_Empty then
               declare
                  Pick : constant Entity_Id := Todo.Proof.First_Element;

               begin
                  Done.Proof.Insert (Pick);

                  if Scope_Truly_Within_Or_Same (Pick, Analyzed) then

                     Crash_On_Abstract_Callee (Pick);

                     declare
                        Picked : Call_Nodes renames
                          Contracts (Pick).Globals.Calls;

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
                  Pick : constant Entity_Id := Todo.Other.First_Element;

               begin
                  Done.Other.Insert (Pick);

                  if Scope_Truly_Within_Or_Same (Pick, Analyzed) then

                     Crash_On_Abstract_Callee (Pick);

                     declare
                        Picked : Call_Nodes renames
                          Contracts (Pick).Globals.Calls;

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

         Node_Sets.Move (Target => O_Proof,
                         Source => Done.Proof);
      end Find_Proof_Calls;

      --  Finally, overlapping. For proof calls it is just like in slicing.
      --  However, calls that are both conditional and definitive are resolved
      --  in slicing as definitive, but here as conditional.
      --
      --  It is because in slicing we are synthesizing contract for the sliced
      --  subprogram; if its callee is called definitely then its outputs will
      --  become outputs of the sliced subprogram (and it doesn't matter if it
      --  is also called conditionally). Here we categorize calls to use their
      --  contracts; if a callee is called conditionally then we must read its
      --  outputs (and it doesn't matter if it is also called definitively).

      return (Proof_Calls       => O_Proof - O_Conditional - O_Definite,
              Conditional_Calls => O_Conditional,
              Definite_Calls    => O_Definite - O_Conditional);
   end Categorize_Calls;

   --------------------
   -- Contract_Calls --
   --------------------

   function Contract_Calls (E : Entity_Id) return Node_Sets.Set is
      Calls : Node_Sets.Set;

      procedure Collect_Calls (Expr : Node_Id);
      --  Collect function calls in expression Expr and put them in Calls

      -------------------
      -- Collect_Calls --
      -------------------

      procedure Collect_Calls (Expr : Node_Id) is
      begin
         Calls.Union (Get_Functions (Expr, Include_Predicates => True));
      end Collect_Calls;

   --  Start of processing for Contract_Calls

   begin
      for Expr of Get_Precondition_Expressions (E) loop
         Collect_Calls (Expr);
      end loop;

      for Expr of Get_Postcondition_Expressions (E, Refined => False)
      loop
         Collect_Calls (Expr);
      end loop;

      return Calls;
   end Contract_Calls;

   ----------------------
   -- Contract_Globals --
   ----------------------

   function Contract_Globals
     (E : Entity_Id;
      Refined : Boolean)
      return Global_Nodes
   is
      Globals : Global_Flow_Ids;

   begin
      Get_Globals
        (Subprogram          => E,
         Scope               => Get_Flow_Scope (if Refined
                                                then Get_Body_Entity (E)
                                                else E),
         Classwide           => False,
         Globals             => Globals,
         Use_Deduced_Globals => False);

      --  Constants without variable inputs should not appear in Global/Depends
      --  contracts in the first place, but users might put them there by
      --  mistake. We will detect this when analyzing the invalid contracts,
      --  but here we still want to filter them to stop propagation of errors
      --  and prevent failures on (otherwise reasonable) assertions.
      --
      --  ??? probably something weird might happen if a constant without
      --  variable input appears in Global/Depends of a "boundary" subprogram,
      --  i.e. either subprogram which has no-body-yet or is declared in .ads
      --  file excluded from the analysis by GPR's Excluded_Source_Files
      --  directive.

      Remove_Constants (Globals.Proof_Ins);
      Remove_Constants (Globals.Inputs);

      return (Proof_Ins => To_Node_Set (Globals.Proof_Ins),
              Inputs    => To_Node_Set (Globals.Inputs),
              Outputs   => To_Node_Set (Globals.Outputs));
   end Contract_Globals;

   --------------
   -- Disjoint --
   --------------

   function Disjoint (A, B, C : Node_Sets.Set) return Boolean is
   begin
      return not
        (for some E of A => B.Contains (E) or else C.Contains (E))
          or else
        (for some E of B => C.Contains (E));
   end Disjoint;

   -----------
   -- Debug --
   -----------

   procedure Debug (Label : String; E : Entity_Id) is
   begin
      if XXX then
         Ada.Text_IO.Put_Line (Label & " " & Full_Source_Name (E));
      end if;
   end Debug;

   ---------------
   -- Do_Global --
   ---------------

   procedure Do_Global
     (Analyzed  :        Entity_Id;
      Contracts : in out Entity_Contract_Maps.Map)
   is
   begin
      Current_Error_Node := Analyzed;

      for Child of Scope_Map (Analyzed) loop
         Do_Global (Child, Contracts);
      end loop;

      if Analyzed = Root_Entity
        or else not Is_Leaf (Analyzed)
      then
         declare
            Patches : Global_Patch_Lists.List;

         begin
            Fold (Analyzed  => Analyzed,
                  Folded    => Analyzed,
                  Contracts => Contracts,
                  Patches   => Patches);
            --  ### We do call fold here (even if the root is a leaf)
            --  because we've done the refined globals and we need to
            --  consider what goes into the spec.

            for Patch of Patches loop
               Contracts (Patch.Entity).Globals := Patch.Globals;
            end loop;
         end;
      end if;

      --  ??? this is probably wrong place to filter locals
      --  ### Nah, I think this is the right place.
      declare
         C : Contract renames Contracts (Analyzed);
         S : constant Entity_Id := Scope (Analyzed);

      begin
         Filter_Local (Analyzed, C.Globals.Proper);
         Filter_Local (Analyzed, C.Globals.Refined);

         --  Protected type appear as an implicit parameter to protected
         --  subprograms and protected entries, and as a global to things
         --  nested in them. After resolving calls from protected
         --  subprograms and protected entries to their nested things the
         --  type will also appear as a global of the protected
         --  subprogram/entry. Here we strip it. ??? Conceptually this
         --  belongs to Filter_Local where Scope_Same_Or_Within does not
         --  capture this.

         if Ekind (S) = E_Protected_Type then
            C.Globals.Proper.Inputs.Exclude (S);
            C.Globals.Proper.Outputs.Exclude (S);
            C.Globals.Proper.Proof_Ins.Exclude (S);
            C.Globals.Refined.Inputs.Exclude (S);
            C.Globals.Refined.Outputs.Exclude (S);
            C.Globals.Refined.Proof_Ins.Exclude (S);
         end if;
      end;

      if XXX then
         Debug_Traversal (Analyzed);
         Dump (Contracts, Analyzed);
      end if;
   end Do_Global;

   ----------
   -- Dump --
   ----------

   procedure Dump
     (Contracts : Entity_Contract_Maps.Map;
      Analyzed  : Entity_Id)
   is
      procedure Dump (E : Entity_Id);

      procedure Dump (Label : String; Vars : Node_Sets.Set);

      ----------
      -- Dump --
      ----------

      procedure Dump (E : Entity_Id) is

         procedure Dump (Label : String; G : Global_Nodes);
         --  Display globals, if any

         ----------
         -- Dump --
         ----------

         procedure Dump (Label : String; G : Global_Nodes) is
         begin
            if not Is_Empty (G) then
               Ada.Text_IO.Put_Line (Indent & Indent & Label & " =>");
               Dump (Indent & Indent & "Proof_Ins  ", G.Proof_Ins);
               Dump (Indent & Indent & "Inputs     ", G.Inputs);
               Dump (Indent & Indent & "Outputs    ", G.Outputs);
            end if;
         end Dump;

         --  Local constants

         C : constant Entity_Contract_Maps.Cursor := Contracts.Find (E);

      --  Start of processing for Dump

      begin
         for Child of Scope_Map (E) loop
            Dump (Child);
         end loop;

         if Entity_Contract_Maps.Has_Element (C) then
            declare
               Contr     : Contract renames Contracts (C);
               Highlight : constant Boolean := E = Analyzed;

            begin
               if Highlight then
                  Term_Info.Set_Style (Bright);
               end if;

               Ada.Text_IO.Put_Line (Indent &
                                       Ekind (E)'Image & ": " &
                                       Full_Source_Name (E));

               if Highlight then
                  Term_Info.Set_Style (Normal);
               end if;

               Dump ("Global",         Contr.Globals.Proper);
               Dump ("Refined_Global", Contr.Globals.Refined);

               if not Contr.Globals.Calls.Proof_Calls.Is_Empty
                 or else not Contr.Globals.Calls.Conditional_Calls.Is_Empty
                 or else not Contr.Globals.Calls.Definite_Calls.Is_Empty
--                   or else not Contr.Remote_Calls.Is_Empty
               then
                  Ada.Text_IO.Put_Line (Indent & Indent & "Calls:");
                  Dump (Indent & Indent & "Proof      ",
                        Contr.Globals.Calls.Proof_Calls);
                  Dump (Indent & Indent & "Conditional",
                        Contr.Globals.Calls.Conditional_Calls);
                  Dump (Indent & Indent & "Definite   ",
                        Contr.Globals.Calls.Definite_Calls);
--                    Dump (Indent & Indent & "Remote     ",
--                          Contr.Remote_Calls);
               end if;

               case Ekind (E) is
                  --  when E_Function | E_Procedure =>
                     --  Ada.Text_IO.Put_Line
                     --    (Indent & Indent & "Nonblocking  : " &
                     --     Boolean'Image (Contr.Nonblocking));
                     --  Ada.Text_IO.Put_Line
                     --    (Indent & Indent & "Nonreturning : " &
                     --     Boolean'Image (Contr.Nonreturning));

                  when E_Package =>
                     Dump (Indent & "Initializes  (proper)",
                           Contr.Globals.Initializes.Proper);

                     Dump (Indent & "Initializes  (refined)",
                           Contr.Globals.Initializes.Refined);

                  when others =>
                     null;
               end case;

               for Kind in Contr.Tasking'Range loop
                  if not Contr.Tasking (Kind).Is_Empty then
                     Dump (Indent & Kind'Img, Contr.Tasking (Kind));
                  end if;
               end loop;
            end;
         end if;
      end Dump;

      procedure Dump (Label : String; Vars : Node_Sets.Set) is
      begin
         if not Vars.Is_Empty then
            Ada.Text_IO.Put (Indent & Label & ":");
            for C in Vars.Iterate loop
               declare
                  Var : Entity_Id renames Vars (C);
                  use type Node_Sets.Cursor;

               begin
                  Ada.Text_IO.Put (" ");

                  declare
                     Highlight : constant Boolean := Var = Analyzed;

                  begin
                     if Highlight then
                        Term_Info.Set_Style (Bright);
                     end if;

                     if Is_Heap_Variable (Var) then
                        Ada.Text_IO.Put (Name_Of_Heap_Variable);
                     else
                        Ada.Text_IO.Put (Full_Source_Name (Var));
                        Ada.Text_IO.Put
                          (" (" & Entity_Kind'Image (Ekind (Var)) & ")");
                     end if;

                     if Highlight then
                        Term_Info.Set_Style (Normal);
                     end if;
                  end;

                  if C /= Vars.Last then
                     Ada.Text_IO.Put (',');
                  end if;
               end;
            end loop;
            Ada.Text_IO.New_Line;
         end if;
      end Dump;

   --  Start of processing for Dump

   begin
      if Debug_Partial_Contracts then
         Dump (Analyzed);
         Ada.Text_IO.New_Line;
      end if;
   end Dump;

   ------------------
   -- Filter_Local --
   ------------------

   procedure Filter_Local (E : Entity_Id; Nodes : in out Node_Sets.Set) is
      Remote : Node_Sets.Set;

   begin
      for N of Nodes loop

         --  Filter variables declared within E and the E itself (which occurs
         --  as a global when E is a single concurrent type). Heaps are never
         --  local variables, so they must be always kept while filtering (we
         --  special-case them because they are have no parents and so would
         --  crash further checks). Also, frontend puts generic actuals of
         --  mode IN directly inside the instance, but from the language point
         --  of view they act as globals (e.g. can appear in the RHS of the
         --  generated Initializes).

         if Is_Heap_Variable (N)
           or else Is_Heap_State (N)
           or else not (Is_In_Analyzed_Files (N)
                        and then Scope_Within_Or_Same (N, E)
                        and then (if In_Generic_Actual (N)
                                  then Scope (N) /= E))
         then
            Remote.Insert (N);
         end if;
      end loop;

      Node_Sets.Move (Target => Nodes,
                      Source => Remote);
   end Filter_Local;

   procedure Filter_Local (E : Entity_Id; G : in out Global_Nodes) is
   begin
      Filter_Local (E, G.Proof_Ins);
      Filter_Local (E, G.Inputs);
      Filter_Local (E, G.Outputs);
   end Filter_Local;

   ----------
   -- Fold --
   ----------

   procedure Fold (Folded    :        Entity_Id;
                   Analyzed  :        Entity_Id;
                   Contracts :        Entity_Contract_Maps.Map;
                   Patches   : in out Global_Patch_Lists.List)
   is
      Folded_Scope : constant Flow_Scope :=
        (Ent => Folded, Part => Visible_Part);
      --  Just like in Flow_Analyse_Entity, we explicitly use the Visible_Part,
      --  because for subprograms without explicit spec Get_Flow_Scope always
      --  returns the Body_Part.

      Full_Contract : Contract renames Contracts (Folded);

      Original : Flow_Nodes renames Full_Contract.Globals;

      function Callee_Globals
        (Callee : Entity_Id;
         Caller : Entity_Id)
         return Global_Nodes
      with Pre => Is_Caller_Entity (Callee);
      --  Returns entities that contribute to the refined globals of Caller due
      --  to a call to Callee.

      function Collect (E : Entity_Id) return Flow_Nodes
      with Pre => Is_Caller_Entity (E),
           Post => Is_Empty (Collect'Result.Proper);
      --  ### This will go through all calls down the tree (so in our
      --  picture if we are at proc_1 we will not look at calls to
      --  pkg, but we do collect calls to proc_2) and collect their
      --  globals (and take care to make for example the output of a
      --  conditional call an in out).
      --
      --  Note this logic is done in Categorize_Calls.

      function Down_Project (G : Global_Nodes; Caller : Entity_Id)
                             return Global_Nodes;

      --------------------
      -- Callee_Globals --
      --------------------

      function Callee_Globals
        (Callee : Entity_Id;
         Caller : Entity_Id)
         return Global_Nodes
      is
      begin
         if Scope_Truly_Within_Or_Same (Callee, Analyzed) then
            declare
               Callee_Globals : Flow_Nodes renames Contracts (Callee).Globals;

            begin
               if Callee = Analyzed
                 or else Parent_Scope (Callee) = Analyzed
               then
                  --  ??? flatten the condition, e.g. make it a function
                  if (case Ekind (Callee) is
                         when E_Package =>
                            Present (Get_Pragma (Callee, Pragma_Initializes)),

                         when Entry_Kind
                            | E_Function
                            | E_Procedure
                            | E_Task_Type
                         =>
                         Entity_In_SPARK (Callee)
                           and then not Entity_Body_In_SPARK (Callee)
                           and then Has_User_Supplied_Globals (Callee),

                         when E_Protected_Type =>
                            Meaningless,

                         when others => raise Program_Error)
                  then
                     Debug ("Folding with down-projected globals:", Callee);
                     return Down_Project (Callee_Globals.Proper, Caller);
                  else
                     Debug ("Folding with refined globals:", Callee);
                     return Callee_Globals.Refined;
                  end if;
               else
                  Debug ("Folding with proper globals:", Callee);
                  return Down_Project (Callee_Globals.Proper, Caller);
               end if;
            end;
         else
            Debug ("Ignoring remote call to", Callee);
            return Global_Nodes'(others => <>);
         end if;
      end Callee_Globals;

      -------------
      -- Collect --
      -------------

      function Collect (E : Entity_Id) return Flow_Nodes is
         Result_Proof_Ins : Node_Sets.Set := Original.Refined.Proof_Ins;
         Result_Inputs    : Node_Sets.Set := Original.Refined.Inputs;
         Result_Outputs   : Node_Sets.Set := Original.Refined.Outputs;
         --  By keeping these sets separate we don't have to care about
         --  maintaing the Global_Nodes invariant; it will be only checked when
         --  returning from this routine.

         Result : Flow_Nodes;

      begin
         --  First collect callees
         Result.Calls := Categorize_Calls (E, Analyzed, Contracts);

         --  Now collect their globals

         for Callee of Result.Calls.Definite_Calls loop
            declare
               G : constant Global_Nodes :=
                 Callee_Globals (Callee, Caller => E);

            begin
               Result_Proof_Ins.Union (G.Proof_Ins);
               Result_Inputs.Union (G.Inputs);
               Result_Outputs.Union (G.Outputs);
            end;
         end loop;

         for Callee of Result.Calls.Proof_Calls loop
            declare
               G : constant Global_Nodes :=
                 Callee_Globals (Callee, Caller => E);

            begin
               Result_Proof_Ins.Union (G.Proof_Ins);
               Result_Proof_Ins.Union (G.Inputs);
               Result_Outputs.Union (G.Outputs);
            end;
         end loop;

         --  For conditional calls do as above, but also connect the caller's
         --  Inputs vertices to the callee's Outputs vertices. This models code
         --  like:
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
               G : constant Global_Nodes :=
                 Callee_Globals (Callee, Caller => E);

            begin
               Result_Proof_Ins.Union (G.Proof_Ins);
               Result_Inputs.Union (G.Inputs);
               Result_Inputs.Union (G.Outputs);
               Result_Outputs.Union (G.Outputs);
            end;
         end loop;

         --  Post-processing
         --  ### To maintain the non-overlapping invariant
         Result_Proof_Ins.Difference (Result_Inputs);

         declare
            Proof_Ins_Outs : constant Node_Sets.Set :=
              Result_Proof_Ins and Result_Outputs;

         begin
            Result_Proof_Ins.Difference (Proof_Ins_Outs);
            Result_Inputs.Union (Proof_Ins_Outs);
         end;

         Result.Refined := (Proof_Ins => Result_Proof_Ins,
                            Inputs    => Result_Inputs,
                            Outputs   => Result_Outputs);

         return Result;
      end Collect;

      ------------------
      -- Down_Project --
      ------------------

      function Down_Project (G : Global_Nodes; Caller : Entity_Id)
                             return Global_Nodes
      is
         Analyzed_View : constant Flow_Scope :=
           (case Ekind (Caller) is
               when Entry_Kind
                  | E_Function
                  | E_Procedure
                  | E_Protected_Type
                  | E_Task_Type
               =>
                  Get_Flow_Scope (Get_Body (Caller)),

               when E_Package
               =>
                 (Caller, Body_Part),

               when others
               =>
                 raise Program_Error);

      begin
         return
           Global_Nodes'
             (Proof_Ins => Down_Project (G.Proof_Ins, Analyzed_View),
              Inputs    => Down_Project (G.Inputs,    Analyzed_View),
              Outputs   => Down_Project (G.Outputs,   Analyzed_View));
      end Down_Project;

      --  Local variables

      Update : Flow_Nodes;

   --  Start of processing for Fold

   begin
      Debug ("Folding", Folded);

      Update := Collect (Folded);

      Up_Project (Update.Refined, Update.Proper, Folded_Scope);

      --  Handle package Initializes aspect
      if Ekind (Folded) = E_Package then

         --  For package with explicit Initializes bypass the up-projection
         --  ??? at least until we make the up-projection for packages as
         --  robust as it is for subprograms (where such a bypass is not
         --  needed and explicit contracts are passed without modification).

         if Present (Get_Pragma (Folded, Pragma_Initializes)) then
            Update.Initializes.Proper := Original.Initializes.Proper;
         else
            declare
               Projected, Partial : Node_Sets.Set;

            begin
               Update.Initializes.Refined :=
                 Original.Initializes.Refined or
                 ((Update.Refined.Outputs - Update.Refined.Inputs)
                    and
                  Full_Contract.Local_Variables);

               Up_Project (Update.Initializes.Refined, Folded_Scope,
                           Projected, Partial);

               for State of Partial loop
                  if Is_Fully_Contained (State, Update.Initializes.Refined,
                                         Folded_Scope)
                  then
                     Projected.Include (State);
                  end if;
               end loop;

               --  Add states that are trivially initialized because they
               --  have null refinements (their initialization is missed
               --  while looking at the initialization of the constituents).

               if Has_Non_Null_Abstract_State (Folded)
                 and then Entity_Body_In_SPARK (Folded)
               then
                  for State of Iter (Abstract_States (Folded)) loop
                     if Has_Null_Refinement (State) then
                        Projected.Insert (State);
                     end if;
                  end loop;
               end if;

               Node_Sets.Move (Target => Update.Initializes.Proper,
                               Source => Projected);
            end;
         end if;
      end if;

      Filter_Local (Analyzed, Update.Calls.Proof_Calls);
      Filter_Local (Analyzed, Update.Calls.Definite_Calls);
      Filter_Local (Analyzed, Update.Calls.Conditional_Calls);

      --  Filter_Local (Analyzed, Update.Remote_Calls);
      --  ### Remove this above commented out

      Patches.Append (Global_Patch'(Entity  => Folded,
                                    Globals => Update));

      for Child of Scope_Map (Folded) loop
         Fold (Child, Analyzed, Contracts, Patches);
      end loop;
   end Fold;

   --------------------
   -- Frontend_Calls --
   --------------------

   function Frontend_Calls (E : Entity_Id) return Node_Sets.Set
     renames Computed_Calls;

   ----------------------
   -- Frontend_Globals --
   ----------------------

   function Frontend_Globals (E : Entity_Id) return Global_Nodes is
      Inputs  : Node_Sets.Set;
      Outputs : Node_Sets.Set;

      function Remove_Constants_Without_Variable_Input
        (Nodes : Node_Sets.Set)
         return Node_Sets.Set
      with Post =>
          Remove_Constants_Without_Variable_Input'Result.Is_Subset
            (Of_Set => Nodes);
      --  Frontend attempts to reject constants without variable input, but
      --  uses criteria that (necessarily) doesn't know about SPARK_Mode of
      --  their full views. We need to reject some globals that it misses.

      ---------------------------------------------
      -- Remove_Constants_Without_Variable_Input --
      ---------------------------------------------

      function Remove_Constants_Without_Variable_Input
        (Nodes : Node_Sets.Set)
         return Node_Sets.Set
      is
         Result : Node_Sets.Set;
      begin
         for N of Nodes loop
            if Ekind (N) = E_Constant then
               if Has_Variable_Input (N) then
                  Result.Insert (N);
               end if;

            else
               Result.Insert (N);
            end if;
         end loop;

         return Result;
      end Remove_Constants_Without_Variable_Input;

   --  Start of processing for Frontend_Globals

   begin
      --  Collect frontend globals using only info from the current compilation
      --  unit.
      Collect_Direct_Computed_Globals (E, Inputs, Outputs);

      return (Inputs    => Remove_Constants_Without_Variable_Input (Inputs),
              Outputs   => Remove_Constants_Without_Variable_Input (Outputs),
              Proof_Ins => <>);

   end Frontend_Globals;

   ------------------------
   -- Generate_Contracts --
   ------------------------

   procedure Generate_Contracts (GNAT_Root : Node_Id) is
      procedure GG_Register_Flow_Scopes is
        new Iterate_Flow_Scopes (GG_Register_Flow_Scope);

   begin
      Dump_Tree;

      --  GG section in ALI must be present, even if it is empty
      GG_Write_Initialize (GNAT_Root);

      --  Ignore compilation units that only rename other units; the renamings
      --  are expanded by the frontend.

      if Present (Root_Entity) then
         declare
            Contracts : Entity_Contract_Maps.Map;
            --  Partial information collected by analysis of inner scopes
            --  needed for the summary of their outer scopes.

            Constant_Graph : Constant_Graphs.Graph;
            --  Graph with dependencies between constants and their variable
            --  inputs.

         begin
            --  Load frontend cross-references (for subprograms with SPARK_Mode
            --  => Off), except for the "no Global means Global => null" mode;
            --  they will be picked in Do_Preanalysis below.

            if Gnat2Why_Args.Flow_Generate_Contracts then
               Load_SPARK_Xrefs;
            end if;

            Do_Preanalysis (Contracts);

            if Gnat2Why_Args.Flow_Generate_Contracts then
               Do_Global (Root_Entity, Contracts);
            end if;

            Resolve_Constants (Contracts, Constant_Graph);

            Write_Contracts_To_ALI (Root_Entity, Constant_Graph, Contracts);

            Write_Constants_To_ALI (Constant_Graph);
         end;
      end if;

      GG_Register_Flow_Scopes;

      GG_Write_Finalize;

      if Gnat2Why_Args.Flow_Advanced_Debug then
         Term_Info.Set_Fg (Yellow);
         Ada.Text_IO.Put_Line ("Global generation complete for current CU");
         Term_Info.Set_Fg (Reset);
      end if;
   end Generate_Contracts;

   ---------------
   -- Is_Callee --
   ---------------

   function Is_Callee (E : Entity_Id) return Boolean is
   begin
      return Is_Callable (E)
        or else (Ekind (E) = E_Package
                 and then not Is_Compilation_Unit (E));
   end Is_Callee;

   --------------
   -- Is_Empty --
   --------------

   function Is_Empty (G : Global_Nodes) return Boolean is
     (G.Proof_Ins.Is_Empty and then
      G.Inputs.Is_Empty and then
      G.Outputs.Is_Empty);

   -----------------
   -- Is_Callable --
   -----------------

   function Is_Callable (E : Entity_Id) return Boolean is
     (Ekind (E) in Entry_Kind | E_Function | E_Procedure);

   --------------------
   -- Do_Preanalysis --
   --------------------

   procedure Do_Preanalysis
     (Contracts : in out Entity_Contract_Maps.Map)
   is
      procedure Preanalyze (E : Entity_Id);

      ----------------
      -- Preanalyze --
      ----------------

      procedure Preanalyze (E : Entity_Id) is
         Contr : Contract;
         --  Contract for the analyzed entity

      begin
         Current_Error_Node := E;

         --  This is first traversal of the current compilation unit, so it's
         --  a good place for some debug.
         Debug_Traversal (E);

         case Ekind (E) is
            when Entry_Kind
               | E_Function
               | E_Procedure
               | E_Task_Type
            =>
               Contr := (if Entity_In_SPARK (E)
                         and then
                           (Entity_Body_In_SPARK (E)
                            or else
                              (Is_Expression_Function_Or_Completion (E)
                               and then
                               Entity_Body_Compatible_With_SPARK (E)))
                         then Preanalyze_Body (E)
                         else Preanalyze_Spec (E));

            when E_Package =>
               Contr := (if Entity_In_SPARK (E)
                         then Preanalyze_Body (E)
                         else Preanalyze_Spec (E));

            when E_Protected_Type =>
               --   ??? perhaps we should do something, but now we don't
               null;

            when others =>
               raise Program_Error;
         end case;

         --  Terminating stuff, picked no matter if body is in SPARK
         Contr.Has_Terminate :=
           (if Is_Callable (E)
            then Has_Terminate_Annotation (E)
            else Meaningless);

         --  Subprogram_Variant stuff, picked no matter if body is in SPARK.
         --  Nested packages inherit the Subprogram_Variant aspect from their
         --  enclosing subprogram, for termination analysis purposes.
         Contr.Has_Subp_Variant :=
           (if Is_Callable (E)
               or else (Ekind (E) = E_Package
                        and then not Is_Library_Level_Entity (E))
            then Has_Subprogram_Variant
              (Subprograms.Enclosing_Subprogram (E))
            else Meaningless);

         Contr.Calls_Current_Task :=
           Includes_Current_Task (Contr.Direct_Calls);

         Contracts.Insert (E, Contr);
      end Preanalyze;

   begin
      Iterate_Main_Unit (Preanalyze'Access);

      --  Only debug output from now on

      if XXX then
         Ada.Text_IO.Put_Line ("Pre-analyzed contracts:");
         Dump (Contracts, Root_Entity);
      end if;
   end Do_Preanalysis;

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
         E : constant Entity_Id := G.Get_Key (V);
      begin
         if E = Variable_Input then
            return (Show        => True,
                    Shape       => Node_Shape_T'First,
                    Colour      => Null_Unbounded_String,
                    Fill_Colour => To_Unbounded_String ("gray"),
                    Label       => To_Unbounded_String ("Variable input"));
         else
            return (Show        => True,
                    Shape       => (if Ekind (E) = E_Constant
                                    then Shape_Oval
                                    else Shape_Box),
                    Colour      => Null_Unbounded_String,
                    Fill_Colour => Null_Unbounded_String,
                    Label       => To_Unbounded_String (Full_Source_Name (E)));
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
        Unique_Name (Unique_Main_Unit_Entity) & "_constants_1";
      --  ??? this fails on subprogram instantiation as compilation units

   --  Start of processing for Print_Graph

   begin
      G.Write_Pdf_File
        (Filename  => Filename,
         Node_Info => NDI'Access,
         Edge_Info => EDI'Access);
   end Print;

   -----------------------
   -- Resolve_Constants --
   -----------------------

   procedure Resolve_Constants
     (Contracts      :     Entity_Contract_Maps.Map;
      Constant_Graph : out Constant_Graphs.Graph)
   is
      --  ??? honestly, I just do not know how if we should care about both
      --  refined and abstract globals here.

      Todo : Node_Sets.Set;
      --  Entities to be processed (either constants or subprograms called
      --  (directly or indirectly) in their initialization expressions.

      -------------------------------------------------------------------------
      --  List utilities
      -------------------------------------------------------------------------

      procedure Append (List : in out Node_Lists.List; Set : Node_Sets.Set)
      with Post => List.Length = List'Old.Length + Set.Length;

      -------------------------------------------------------------------------
      --  Specs
      -------------------------------------------------------------------------

      function Represent_Variable_Inputs
        (Inputs : Node_Lists.List)
         return Boolean
      is
        (Inputs = Variable
           or else
        (for all E of Inputs =>
           Ekind (E) in E_Constant | Entry_Kind | E_Function | E_Procedure))
        with Ghost;
      --  A sanity-checking utility for routines that grow the constant graph

      function Direct_Inputs_Of_Constant
        (E : Entity_Id)
         return Node_Lists.List
        with Pre  => Ekind (E) = E_Constant and then Has_Variable_Input (E),
             Post => Represent_Variable_Inputs
                        (Direct_Inputs_Of_Constant'Result);
      --  Returns variable inputs of the initialization of constant E

      function Direct_Inputs_Of_Subprogram
        (E : Entity_Id)
         return Node_Lists.List
        with Pre  => Ekind (E) in Entry_Kind | E_Function | E_Procedure,
             Post => Represent_Variable_Inputs
                        (Direct_Inputs_Of_Subprogram'Result);
      --  Returns variable inputs coming from the globals or calls of
      --  subprogram E.

      function Pick_Constants (From : Global_Set) return Node_Lists.List
      with Post => Pick_Constants'Result.Length <= From.Length
                     and then
                   (for all E of Pick_Constants'Result =>
                      Ekind (E) = E_Constant);
      --  Selects constants from the given set

      procedure Seed (E : Entity_Id)
      with Pre => Ekind (E) = E_Constant;
      --  Seed the Constant_Graph and Todo with constant E

      procedure Seed (L : Node_Lists.List);
      --  Same as above, but lifted to lists

      procedure Seed_Exposed_Constant (E : Entity_Id)
      with Pre => Ekind (E) = E_Constant;
      --  Seed the constant graph with E if it is exposed to other compilation
      --  units (roughly speaking, if it is declared in the .ads file of a
      --  package-unit).

      -------------------------------------------------------------------------
      --  Bodies
      -------------------------------------------------------------------------

      ------------
      -- Append --
      ------------

      procedure Append (List : in out Node_Lists.List; Set : Node_Sets.Set) is
      begin
         for E of Set loop
            List.Append (E);
         end loop;
      end Append;

      -------------------------------
      -- Direct_Inputs_Of_Constant --
      -------------------------------

      function Direct_Inputs_Of_Constant
        (E : Entity_Id)
         return Node_Lists.List
      is
         Full : Entity_Id;
         Expr : Node_Id;
      begin
         --  This routine is intentionally mirrored after Has_Variable_Input;
         --  any change here should be reflected there.

         if Is_Imported (E) then
            return Variable;
         end if;

         Expr := Expression (Declaration_Node (E));
         if Present (Expr) then
            Full := E;
         else
            --  We are dealing with a deferred constant so we need to get to
            --  the full view.
            Full := Full_View (E);
            Expr := Expression (Declaration_Node (Full));
         end if;

         if not Entity_In_SPARK (Full) then
            --  We are dealing with an entity that is not in SPARK so we
            --  assume that it does not have variable input.
            return Node_Lists.Empty_List;
         end if;

         declare
            Variables : constant Flow_Id_Sets.Set :=
              Get_Variables
                (Expr,
                 Scope                => Get_Flow_Scope (Full),
                 Target_Name          => Null_Flow_Id,
                 Fold_Functions       => Inputs,
                 Use_Computed_Globals => False);

            Inputs : Node_Lists.List;

         begin
            --  ??? perhaps this can be rewriten with To_Node_Set,
            --  Has_Variables and Pick_Constants.

            for Var of Variables loop
               declare
                  V : constant Entity_Id := Get_Direct_Mapping_Id (Var);

                  pragma Assert (Is_Global_Entity (V));

               begin
                  if Ekind (V) = E_Constant then
                     Inputs.Append (V);
                  else
                     return Variable;
                  end if;
               end;
            end loop;

            --  Only care about functions whose globals couldn't be resolved by
            --  Get_Variables. For subprograms in predefined units with no
            --  Global contract we assume Global => null, similarly as we do in
            --  Mark_Call.
            --  ??? this code is duplicated in Has_Variable_Input_Internal

            for F of Get_Functions (Expr, Include_Predicates => False) loop
               if not Has_User_Supplied_Globals (F)
                 and then not In_Predefined_Unit (F)
               then
                  Inputs.Append (F);
               end if;
            end loop;

            return Inputs;
         end;
      end Direct_Inputs_Of_Constant;

      ---------------------------------
      -- Direct_Inputs_Of_Subprogram --
      ---------------------------------

      function Direct_Inputs_Of_Subprogram
        (E : Entity_Id)
         return Node_Lists.List
      is
      begin
         --  ??? protected entries and protected subprograms always have
         --  variable input; volatile functions are perhaps similar.

         if Is_In_Analyzed_Files (E) then
            declare
               Globals : Flow_Nodes renames Contracts (E).Globals;

               function Has_Variables (G : Global_Set) return Boolean is
                  (for some C of G => Ekind (C) /= E_Constant);

               Inputs : Node_Lists.List;

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
            end;
         else
            return To_List (E);
         end if;
      end Direct_Inputs_Of_Subprogram;

      --------------------
      -- Pick_Constants --
      --------------------

      function Pick_Constants (From : Global_Set) return Node_Lists.List is
         Constants : Node_Lists.List;
      begin
         for E of From loop
            if Present (E)
              and then Ekind (E) = E_Constant
            then
               Constants.Append (E);
            end if;
         end loop;

         return Constants;
      end Pick_Constants;

      ----------
      -- Seed --
      ----------

      procedure Seed (E : Entity_Id) is
      begin
         Todo.Include (E);
         Constant_Graph.Include_Vertex (E);
      end Seed;

      procedure Seed (L : Node_Lists.List) is
      begin
         for E of L loop
            Seed (E);
         end loop;
      end Seed;

      ---------------------------
      -- Seed_Exposed_Constant --
      ---------------------------

      procedure Seed_Exposed_Constant (E : Entity_Id) is
      begin
         --  ??? test for such packages should be more restrictive
         if Ekind (Scope (E)) = E_Package then
            Seed (E);
         end if;
      end Seed_Exposed_Constant;

      procedure Seed_Exposed_Constants is
         new Iterate_Constants_In_Main_Unit (Seed_Exposed_Constant);

   --  Start of processing for Resolve_Constants

   begin
      Constant_Graph := Constant_Graphs.Create;

      --  Add hardcoded representation of the variable input

      Constant_Graph.Add_Vertex (Variable_Input);

      --  We lazily only care about constants referenced in the Global
      --  contracts of the units of the current compilation unit
      --  (including packages, which must have an implicit Global).
      --  Initialize the workset with constants from the generated globals
      --  ??? better to initialize this when globals are picked from the AST

      Seed_Exposed_Constants;

      --  However, it is also our responsibility to record calls in the
      --  initialization expressions of constants exposed from the current
      --  compilation unit, i.e. declared in the visible and private parts
      --  of .ads packages.

      for Contr of Contracts loop
         Seed (Pick_Constants (Contr.Globals.Refined.Proof_Ins));
         Seed (Pick_Constants (Contr.Globals.Refined.Inputs));
      end loop;

      --  Grow graph

      while not Todo.Is_Empty loop
         declare
            E : constant Entity_Id := Todo (Todo.First);

            Variable_Inputs : constant Node_Lists.List :=
              (case Ekind (E) is
                  when E_Constant =>
                     Direct_Inputs_Of_Constant (E),

                  when Entry_Kind | E_Function | E_Procedure =>
                     Direct_Inputs_Of_Subprogram (E),

                  when others =>
                     raise Program_Error);

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

      if Gnat2Why_Args.Flow_Advanced_Debug then
         Print (Constant_Graph);
      end if;

      Constant_Graph.Close;

   end Resolve_Constants;

   ---------------------
   -- Resolved_Inputs --
   ---------------------

   function Resolved_Inputs
     (E              : Entity_Id;
      Constant_Graph : Constant_Graphs.Graph)
      return Node_Lists.List
   is
      Inputs : Node_Lists.List;
   begin
      if Constant_Graph.Edge_Exists (E, Variable_Input) then
         return Variable;
      else
         for V of
           Constant_Graph.Get_Collection
             (Constant_Graph.Get_Vertex (E),
              Constant_Graphs.Out_Neighbours)
         loop
            declare
               Input : constant Entity_Id :=
                 Constant_Graph.Get_Key (V);

            begin
               if Ekind (Input) in E_Function | E_Procedure
                 and then not Is_In_Analyzed_Files (Input)
               then
                  Inputs.Append (Input);
               end if;
            end;
         end loop;

         return Inputs;
      end if;
   end Resolved_Inputs;

   ---------------------
   -- Strip_Constants --
   ---------------------

   procedure Strip_Constants
     (From           : in out Flow_Nodes;
      Constant_Graph :        Constant_Graphs.Graph)
   is

      procedure Strip (From : in out Global_Nodes);
      procedure Strip (From : in out Global_Set)
        with Post => From.Is_Subset (From'Old);

      -----------
      -- Strip --
      -----------

      procedure Strip (From : in out Global_Nodes) is
      begin
         Strip (From.Proof_Ins);
         Strip (From.Inputs);
      end Strip;

      procedure Strip (From : in out Global_Set) is
         Filtered : Node_Sets.Set;
      begin
         for E of From loop
            if Present (E)
              and then Ekind (E) = E_Constant
            then
               if not Resolved_Inputs (E, Constant_Graph).Is_Empty then
                  Filtered.Insert (E);
               end if;
            else
               Filtered.Insert (E);
            end if;
         end loop;

         Node_Sets.Move (Target => From,
                         Source => Filtered);
      end Strip;

   --  Start of processing for Strip_Constants

   begin
      Strip (From.Proper);
      Strip (From.Refined);
      Strip (From.Initializes.Proper);
      Strip (From.Initializes.Refined);
      --  ??? stripping the refined Initializes is excessive, because currently
      --  they are not written to the ALI file but that needs to be revisited
   end Strip_Constants;

   ----------------------------
   -- Write_Constants_To_ALI --
   ----------------------------

   procedure Write_Constants_To_ALI (Constant_Graph : Constant_Graphs.Graph) is
      procedure Write_Constant (E : Entity_Id);

      --------------------
      -- Write_Constant --
      --------------------

      procedure Write_Constant (E : Entity_Id) is
      begin
         --  Locals represent all constants "owned" by a scope from the current
         --  compilation unit, but we are only interested in those which were
         --  seeded into constant graph.
         --  ??? the graph might include constants that were not seeded, but
         --  added while growing it; but this over-approximation is safe.

         if Constant_Graph.Contains (E) then
            declare
               Inputs : constant Node_Lists.List :=
                 Resolved_Inputs (E, Constant_Graph);

            begin
               --  If we know that constant has variable input, then don't even
               --  register it in the ALI file, so it will be treated as an
               --  ordinary global (i.e. variable).

               if Inputs /= Variable then
                  GG_Register_Constant_Calls (E, Inputs);
               end if;
            end;
         end if;
      end Write_Constant;

      procedure Write_Constants is
         new Iterate_Constants_In_Main_Unit (Write_Constant);

   --  Start of processing for Write_Constants_To_ALI

   begin
      Write_Constants;
   end Write_Constants_To_ALI;

   ----------------------------
   -- Write_Contracts_To_ALI --
   ----------------------------

   procedure Write_Contracts_To_ALI
     (E              :        Entity_Id;
      Constant_Graph :        Constant_Graphs.Graph;
      Contracts      : in out Entity_Contract_Maps.Map)
   is
      Contr : Contract renames Contracts (E);

   begin
      for Child of Scope_Map (E) loop
         Write_Contracts_To_ALI (Child, Constant_Graph, Contracts);
      end loop;

      if Ekind (E) /= E_Protected_Type then

         Strip_Constants (Contr.Globals, Constant_Graph);

         GG_Register_Direct_Calls (E, Contr.Direct_Calls);

         GG_Register_Global_Info
           (E                => E,
            Local            => not Is_Visible_From_Other_Units (E),
            Is_Protected     => Ekind (E) in E_Function | E_Procedure
                                 and then Ekind (Scope (E)) =
                                          E_Protected_Type,
            Is_Library_Level => Ekind (E) = E_Package
                                 and then Is_Library_Level_Entity (E),
            Origin           => Origin_Flow,      --  ??? dummy
            Globals          => Contr.Globals,

            Local_Variables  => (if Ekind (E) = E_Package
                                 then States_And_Objects (E)
                                 else Node_Sets.Empty_Set),

            Has_Terminate    => Contr.Has_Terminate,
            Has_Subp_Variant => Contr.Has_Subp_Variant,
            Nonreturning     => Contr.Nonreturning,
            Nonblocking      => Contr.Nonblocking,

            Entries_Called   => Contr.Entry_Calls,
            Tasking          => Contr.Tasking);
      end if;

   end Write_Contracts_To_ALI;

end Flow_Generated_Globals.Partial;
