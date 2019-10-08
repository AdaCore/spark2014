------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                                 F L O W                                  --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                Copyright (C) 2013-2019, Altran UK Limited                --
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

with Ada.Containers;
with Ada.Containers.Hashed_Maps;
with Ada.Containers.Hashed_Sets;
with Ada.Strings.Unbounded;      use Ada.Strings.Unbounded;
with Atree;                      use Atree;
with Common_Containers;          use Common_Containers;
with Einfo;                      use Einfo;
with Flow_Dependency_Maps;       use Flow_Dependency_Maps;
with Flow_Types;                 use Flow_Types;
with Graphs;
with Types;                      use Types;

package Flow is

   ----------------------------------------------------------------------
   --  Common abbreviations and acronyms
   --
   --  Through the Flow.* package hierarchy, the following abbreviations
   --  and acronyms are used:
   --
   --  CDG  - Control Dependence Graph
   --  CFG  - Control Flow Graph
   --  DDG  - Data Dependence Graph
   --  IPFA - Interprocedural Flow Analysis
   --  PDG  - Program Dependence Graph
   --  TDG  - Transitive Dependence Graph
   ----------------------------------------------------------------------

   ----------------------------------------------------------------------
   --  Flow_Graphs
   ----------------------------------------------------------------------

   package Flow_Graphs is new Graphs
     (Vertex_Key   => Flow_Id,
      Key_Hash     => Hash,
      Edge_Colours => Edge_Colours,
      Null_Key     => Null_Flow_Id,
      Test_Key     => "=");

   package Attribute_Maps is new Ada.Containers.Hashed_Maps
     (Key_Type        => Flow_Graphs.Vertex_Id,
      Element_Type    => V_Attributes,
      Hash            => Flow_Graphs.Vertex_Hash,
      Equivalent_Keys => Flow_Graphs."=");

   procedure Print_Graph_Vertex (G : Flow_Graphs.Graph;
                                 M : Attribute_Maps.Map;
                                 V : Flow_Graphs.Vertex_Id);
   --  Print a human-readable representation for the given vertex.

   ----------------------------------------------------------------------
   --  Utility packages
   ----------------------------------------------------------------------

   package Vertex_Sets is new Ada.Containers.Hashed_Sets
     (Element_Type        => Flow_Graphs.Vertex_Id,
      Hash                => Flow_Graphs.Vertex_Hash,
      Equivalent_Elements => Flow_Graphs."=",
      "="                 => Flow_Graphs."=");

   package Vertex_To_Vertex_Set_Maps is new Ada.Containers.Hashed_Maps
     (Key_Type        => Flow_Graphs.Vertex_Id,
      Element_Type    => Vertex_Sets.Set,
      Hash            => Flow_Graphs.Vertex_Hash,
      Equivalent_Keys => Flow_Graphs."=",
      "="             => Vertex_Sets."=");

   ----------------------------------------------------------------------
   --  Flow_Analysis_Graphs
   ----------------------------------------------------------------------

   --  ??? This should be a variant record, but O325-005 and AI12-0047 make
   --      this difficult.
   type Flow_Global_Generation_Info is record
      Globals : Global_Set;
      --  Non-local variables and parameters other than those of the analyzed
      --  entity.

      Local_Variables : Node_Sets.Set;
      --  Only for packages; represents the refined view of what can appear on
      --  the LHS of the generated Initializes contract.
   end record;

   type Entry_Call is record
      Prefix : Node_Id;      --  prefix of an entry call
      Entr   : Entity_Id;    --  protected entry
   end record
   with Predicate => Is_Entry (Entry_Call.Entr);
   --  Unique representation of a call to protected entry of a library-level
   --  protected object.

   function Hash (E : Entry_Call) return Ada.Containers.Hash_Type;
   --  Hash function needed to instantiate container package

   package Entry_Call_Sets is new Ada.Containers.Hashed_Sets
     (Element_Type        => Entry_Call,
      Hash                => Hash,
      Equivalent_Elements => "=");

   type Tasking_Info_Kind is (Entry_Calls,
                              Suspends_On,
                              Unsynch_Accesses,
                              Locks);
   pragma Ordered (Tasking_Info_Kind);
   --  Tasking-related information collected for subprograms, entries, tasks
   --  and package elaborations. Used both for ownership (aka. exclusivity)
   --  checks and for ceiling priority protocol checks.

   subtype Tasking_Owning_Kind is Tasking_Info_Kind
     range Entry_Calls ..
           -- Suspends_On
           Unsynch_Accesses;
   --  Tasking-related information used for ownership checks
   --
   --  Note: it is intentionally defined with range and not with
   --  Static_Predicate to allow its use as an array index.

   type Tasking_Info is array (Suspends_On .. Locks) of Node_Sets.Set;
   --  Named array type for sets of nodes related to tasking. The nodes
   --  represent library-level objects.

   type Flow_Analysis_Graphs_Root
     (Kind               : Analyzed_Subject_Kind := Kind_Subprogram;
      Generating_Globals : Boolean               := False)
   is record
      Spec_Entity : Entity_Id;
      B_Scope     : Flow_Scope;
      S_Scope     : Flow_Scope;
      --  The entity and scope (of the body and spec) of the analysed entity.
      --  The two scopes might be the same in some cases.

      Start_Vertex      : Flow_Graphs.Vertex_Id;
      Helper_End_Vertex : Flow_Graphs.Vertex_Id;
      End_Vertex        : Flow_Graphs.Vertex_Id;
      --  The start, helper end and end vertices in the graphs. Start and end
      --  are the obvious, and the helper end is used to indicate the end of
      --  the procedure (i.e. returns jump here), but before postconditions
      --  are checked.

      CFG : Flow_Graphs.Graph;
      DDG : Flow_Graphs.Graph;
      CDG : Flow_Graphs.Graph;
      TDG : Flow_Graphs.Graph;
      PDG : Flow_Graphs.Graph;
      --  The graphs

      Atr : Attribute_Maps.Map;
      --  The vertex attributes for the above graphs.

      Other_Fields : Vertex_To_Vertex_Set_Maps.Map;
      --  For a vertex corresponding to a record field this map will hold a
      --  vertex set of the other record fields; only used in phase 2.

      All_Vars : Flow_Id_Sets.Set;
      --  Flattened variables accessible in the body

      Loops : Node_Sets.Set;
      --  Loops (identified by labels)

      Has_Potentially_Nonterminating_Loops : Boolean;
      --  True for entities that contain loops that may not terminate, i.e. a:
      --  * plain
      --  * while
      --  * for on an iterable container
      --  without Loop_Variant.

      Has_Only_Nonblocking_Statements : Boolean;
      --  True for entities that only contain nonblocking statements

      Base_Filename : Unbounded_String;
      --  A string with the name of the entity that is being analysed. It
      --  follows the convention that we use for naming the .dot and .pdf
      --  files.

      Dependency_Map : Dependency_Maps.Map;
      --  A map of all the dependencies

      Errors_Or_Warnings : Boolean;
      --  True if errors or warnings were found while flow analysing this
      --  entity. This is initialized to False and set to True when an error
      --  or a warning is found.

      Data_Dependency_Errors : Boolean;
      Flow_Dependency_Errors : Boolean;
      --  True if either data or flow dependency error has been reported for
      --  this entity; such errors can be reported from various routines and
      --  those flags are for maintaining a summary.

      Direct_Calls : Node_Sets.Set;
      --  Contains subprograms called and package elaborations

      GG : Flow_Global_Generation_Info;
      --  Information for globals computation

      Entries : Entry_Call_Sets.Set;
      --  Called entries of library-level objects

      Tasking : Tasking_Info;
      --  Tasking-related information collected in phase 1

      Is_Generative : Boolean;
      --  True if we do not have a global contract

      Has_Only_Exceptional_Paths : Boolean;
      --  Set to true if we determine that we have *only* exceptional paths.
      --  This used to avoid emitting some messages, as they might distract
      --  from the actual issue.

      case Kind is
         when Kind_Subprogram | Kind_Task =>
            Is_Main : Boolean;
            --  True if this is a task, a main program, i.e. a library-level
            --  subprogram without formal parameters (global parameters are
            --  allowed) or an interrupt handler.

            Global_N          : Node_Id;
            Refined_Global_N  : Node_Id;
            Depends_N         : Node_Id;
            Refined_Depends_N : Node_Id;
            --  A few contract nodes cached as they can be a tedious to find

         when Kind_Package =>
            Initializes_N : Node_Id;
            --  Contract node cached, since it is tedious to find

            Visible_Vars : Flow_Id_Sets.Set;
            --  Variables visible in the package elaboration

      end case;
   end record;

   function Is_Valid (X : Flow_Analysis_Graphs_Root) return Boolean;

   subtype Flow_Analysis_Graphs is Flow_Analysis_Graphs_Root
   with Dynamic_Predicate => Is_Valid (Flow_Analysis_Graphs);

   package Analysis_Maps is new Ada.Containers.Hashed_Maps
     (Key_Type        => Entity_Id,
      Element_Type    => Flow_Analysis_Graphs,
      Hash            => Node_Hash,
      Equivalent_Keys => "=",
      "="             => "=");

   ----------------------------------------------------------------------
   --  Utilities
   ----------------------------------------------------------------------

   function Loop_Parameter_From_Loop (E : Entity_Id) return Entity_Id
   with Pre  => Ekind (E) = E_Loop,
        Post => No (Loop_Parameter_From_Loop'Result) or else
                Ekind (Loop_Parameter_From_Loop'Result) = E_Loop_Parameter;
   --  Given a loop label, returns the identifier of the loop
   --  parameter or Empty.

   ----------------------------------------------------------------------
   --  Debug
   ----------------------------------------------------------------------

   procedure Print_Graph
     (Filename          : String;
      G                 : Flow_Graphs.Graph;
      M                 : Attribute_Maps.Map;
      Start_Vertex      : Flow_Graphs.Vertex_Id := Flow_Graphs.Null_Vertex;
      Helper_End_Vertex : Flow_Graphs.Vertex_Id := Flow_Graphs.Null_Vertex;
      End_Vertex        : Flow_Graphs.Vertex_Id := Flow_Graphs.Null_Vertex);
   --  Write a dot and pdf file for the given graph.

   ----------------------------------------------------------------------
   --  Main entry to flo analysis
   ----------------------------------------------------------------------

   procedure Flow_Analyse_CUnit (GNAT_Root : Node_Id);
   --  Flow analyses the current compilation unit

   procedure Generate_Globals (GNAT_Root : Node_Id);
   --  Generate flow globals for the current compilation unit

   function Flow_Analyse_Entity
     (E                  : Entity_Id;
      Generating_Globals : Boolean)
      return Flow_Analysis_Graphs
   with Pre => Ekind (E) in E_Function
                          | E_Procedure
                          | E_Task_Type
                          | E_Protected_Type
                          | E_Entry
                          | E_Package
               and then (if Ekind (E) = E_Procedure
                         then not Is_DIC_Procedure (E)
                            and then not Is_Invariant_Procedure (E)
                         elsif Ekind (E) = E_Function
                         then not Is_Predicate_Function (E));
   --  Flow analyse entity E. Do nothing for entities with no body or not in
   --  SPARK 2014.

end Flow;
