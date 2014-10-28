------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                                 F L O W                                  --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                  Copyright (C) 2013-2014, Altran UK Limited              --
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
with Ada.Containers.Vectors;
with Ada.Strings.Unbounded;      use Ada.Strings.Unbounded;

with Atree;                      use Atree;
with Einfo;                      use Einfo;
with Types;                      use Types;

with Common_Containers;          use Common_Containers;

with Graph;
with Flow_Types;                 use Flow_Types;
with Flow_Dependency_Maps;       use Flow_Dependency_Maps;
with Flow_Refinement;            use Flow_Refinement;

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

   package Flow_Graphs is new Graph
     (Vertex_Key        => Flow_Id,
      Edge_Colours      => Edge_Colours,
      Null_Key          => Null_Flow_Id,
      Test_Key          => "=");

   package Attribute_Maps is new Ada.Containers.Hashed_Maps
     (Key_Type        => Flow_Graphs.Vertex_Id,
      Element_Type    => V_Attributes,
      Hash            => Flow_Graphs.Vertex_Hash,
      Equivalent_Keys => Flow_Graphs."=");

   procedure Print_Graph_Vertex (G : Flow_Graphs.T;
                                 M : Attribute_Maps.Map;
                                 V : Flow_Graphs.Vertex_Id);
   --  Print a human-readable representation for the given vertex.

   ----------------------------------------------------------------------
   --  Vertex Pair
   ----------------------------------------------------------------------

   type Vertex_Pair is record
      From : Flow_Graphs.Vertex_Id;
      To   : Flow_Graphs.Vertex_Id;
   end record;

   function "=" (Left, Right : Vertex_Pair) return Boolean is
     (Flow_Graphs."=" (Left.From, Right.From)
        and then Flow_Graphs."=" (Left.To, Right.To));

   function Vertex_Pair_Hash
     (VD : Vertex_Pair)
      return Ada.Containers.Hash_Type;
   --  Hash a Vertex_Pair (useful for building sets of vertex pairs).

   ----------------------------------------------------------------------
   --  Utility packages
   ----------------------------------------------------------------------

   package Node_To_Vertex_Maps is new Ada.Containers.Hashed_Maps
     (Key_Type        => Node_Id,
      Element_Type    => Flow_Graphs.Vertex_Id,
      Hash            => Node_Hash,
      Equivalent_Keys => "=",
      "="             => Flow_Graphs."=");

   package Vertex_Sets is new Ada.Containers.Hashed_Sets
     (Element_Type        => Flow_Graphs.Vertex_Id,
      Hash                => Flow_Graphs.Vertex_Hash,
      Equivalent_Elements => Flow_Graphs."=",
      "="                 => Flow_Graphs."=");

   package Vertex_Vectors is new Ada.Containers.Vectors
     (Index_Type   => Positive,
      Element_Type => Flow_Graphs.Vertex_Id,
      "="          => Flow_Graphs."=");

   package Vertex_To_Vertex_Set_Maps is new Ada.Containers.Hashed_Maps
     (Key_Type        => Flow_Graphs.Vertex_Id,
      Element_Type    => Vertex_Sets.Set,
      Hash            => Flow_Graphs.Vertex_Hash,
      Equivalent_Keys => Flow_Graphs."=",
      "="             => Vertex_Sets."=");

   package Vertex_Pair_Sets is new Ada.Containers.Hashed_Sets
     (Element_Type        => Vertex_Pair,
      Hash                => Vertex_Pair_Hash,
      Equivalent_Elements => "=",
      "="                 => "=");

   ----------------------------------------------------------------------
   --  Flow_Analysis_Graphs
   ----------------------------------------------------------------------

   subtype Valid_Analyzed_Entity is Entity_Kind
     with Static_Predicate =>
       Valid_Analyzed_Entity in E_Subprogram_Body |
                                E_Package |
                                E_Package_Body;

   type Flow_Global_Generation_Info (Present : Boolean) is record
      case Present is
         when True =>
            Aborted     : Boolean;
            --  Set if graph creation, processing or analysis raised some
            --  error; or if the entity should not be analyzed in the first
            --  place.

            Globals     : Node_Sets.Set;
            --  All obvious globals (non-local variables or parameters that
            --  are not subprogram parameters of the analyzed entity).

         when False =>
            null;
      end case;
   end record;

   type Flow_Analysis_Graphs_Root
     (Kind            : Valid_Analyzed_Entity := E_Subprogram_Body;
      Compute_Globals : Boolean               := False)
   is record
      --  Compute_Globals: If true we are trying to compute globals and
      --  will construct the graphs slightly differently. In particular we
      --  will deal with subprogram calls differently and we don't try to
      --  create initial and final vertices for globals.
      --
      --  After we have constructed the graph, we can create a list of
      --  global variables (kinda what the analysis sanity check would do).

      Analyzed_Entity       : Entity_Id;
      B_Scope               : Flow_Scope;
      S_Scope               : Flow_Scope;
      --  The entity and scope (of the body and spec) of the analysed
      --  entity. The two scopes might be the same in some cases.

      Spec_Node             : Entity_Id;
      --  Useful shorthand to the node where the n_contract node is
      --  attached.

      Start_Vertex          : Flow_Graphs.Vertex_Id;
      Helper_End_Vertex     : Flow_Graphs.Vertex_Id;
      End_Vertex            : Flow_Graphs.Vertex_Id;
      --  The start, helper end and end vertices in the graphs. Start and
      --  end are the obvious, and the helper end is used to indicate the
      --  end of the procedure (i.e. returns jump here), but before
      --  postconditions are checked.

      CFG                   : Flow_Graphs.T;
      DDG                   : Flow_Graphs.T;
      CDG                   : Flow_Graphs.T;
      TDG                   : Flow_Graphs.T;
      PDG                   : Flow_Graphs.T;
      --  The graphs.

      Atr                   : Attribute_Maps.Map;
      --  The vertex attributes for the above graphs.

      Other_Fields          : Vertex_To_Vertex_Set_Maps.Map;
      --  For a vertex corresponding to a record field this map will
      --  hold a vertex set of the other record fields.

      Local_Constants       : Node_Sets.Set;
      --  All constants that have been locally declared. This is used as a
      --  workaround to the issue of constants being ignored in general.
      --  This field should be removed once constants, attributes, etc. are
      --  dealt with correctly.

      All_Vars              : Flow_Id_Sets.Set;
      --  A set of all variables used in the body.

      Unmodified_Vars       : Node_Sets.Set;
      --  A set of all variables that are not expected to be modified
      --  because the were named in a pragma Unmodified.

      Unreferenced_Vars     : Node_Sets.Set;
      --  A set of all variables that are not expected to be referenced
      --  because the were named in a pragma Unreferenced.

      Loops                 : Node_Sets.Set;
      --  A set of all loops (identified by label).

      Base_Filename         : Unbounded_String;
      --  A string with the name of the entity that is being analysed.
      --  This string follows the convention that we use for naming the
      --  .dot and .pdf files.

      Aliasing_Present      : Boolean;
      --  True if this subprogram introduces (bad)
      --  aliasing. Subsequent analysis is then meaningless.

      Dependency_Map        : Dependency_Maps.Map;
      --  A map of all the dependencies.

      No_Effects            : Boolean;
      --  True if this is a subprogram with no effects. Certain analysis
      --  are disabled in this case as we would spam the user with error
      --  messages for almost every statement.

      No_Errors_Or_Warnings : Boolean;
      --  True if no errors or warnings were found while flow
      --  analysing this entity. This is initialized to True and set
      --  to False when an error or a warning is found.

      Direct_Calls          : Node_Sets.Set;
      --  All subprograms called

      GG                    : Flow_Global_Generation_Info (Compute_Globals);
      --  Information for globals computation.

      Edges_To_Remove       : Vertex_Pair_Sets.Set;
      --  Set of vertex pairs between which we must not add edges
      --  during the simplification of the graph.

      Lead_To_Abnormal_Termination : Vertex_Sets.Set;
      --  Set of vertices that can lead to an abnormal
      --  termination. This is used to suppress ineffective statement
      --  warnings.

      case Kind is
         when E_Subprogram_Body =>
            Is_Main : Boolean;
            --  True if this is the main program. In order to be the
            --  main it has to be a library level subprogram without
            --  formal parameters (global parameters are allowed).

            Is_Generative : Boolean;
            --  True if we do not have a global contract.

            Last_Statement_Is_Raise : Boolean;
            --  True if the last statement of the subprogram is an
            --  N_Raise_Statement.

            Global_N          : Node_Id;
            Refined_Global_N  : Node_Id;
            Depends_N         : Node_Id;
            Refined_Depends_N : Node_Id;
            --  A few contract nodes cached as they can be a bit
            --  tedious to find.

            Function_Side_Effects_Present : Boolean;
            --  Set to True if we are dealing with a function that has side
            --  effects.

         when E_Package | E_Package_Body =>
            Initializes_N : Node_Id;
            --  A few contract nodes cached as they can be a bit
            --  tedious to find.

            Visible_Vars : Flow_Id_Sets.Set;

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
          Post => not Present (Loop_Parameter_From_Loop'Result) or else
                  Ekind (Loop_Parameter_From_Loop'Result) = E_Loop_Parameter;
   --  Given a loop label, returns the identifier of the loop
   --  parameter or Empty.

   ----------------------------------------------------------------------
   --  Debug
   ----------------------------------------------------------------------

   procedure Print_Graph
     (Filename          : String;
      G                 : Flow_Graphs.T;
      M                 : Attribute_Maps.Map;
      Start_Vertex      : Flow_Graphs.Vertex_Id := Flow_Graphs.Null_Vertex;
      Helper_End_Vertex : Flow_Graphs.Vertex_Id := Flow_Graphs.Null_Vertex;
      End_Vertex        : Flow_Graphs.Vertex_Id := Flow_Graphs.Null_Vertex);
   --  Write a dot and pdf file for the given graph.

   ----------------------------------------------------------------------
   --  Main entry to flo analysis
   ----------------------------------------------------------------------

   procedure Flow_Analyse_CUnit;
   --  Flow analyses the current compilation unit.

   procedure Generate_Flow_Globals (GNAT_Root : Node_Id);
   --  Generate flow globals for the current compilation unit.

private

   function Last_Statement_Is_Raise (E : Entity_Id) return Boolean
     with Pre => Ekind (E) in Subprogram_Kind;
   --  Returns True if the last statement in the
   --  Handled_Sequence_Of_Statements of subprogram E is an
   --  N_Raise_Statement.

   FA_Graphs : Analysis_Maps.Map := Analysis_Maps.Empty_Map;
   --  All analysis results are stashed here in case we need them later. In
   --  particular the Flow.Trivia package makes use of this.

end Flow;
