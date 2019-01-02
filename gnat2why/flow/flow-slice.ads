------------------------------------------------------------------------------
--                                                                          --
--                           GNAT2WHY COMPONENTS                            --
--                                                                          --
--                           F L O W . S L I C E                            --
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

--  This package deals with computing slices (and thus dependency relations)

package Flow.Slice is

   function Dependency
     (FA      : Flow_Analysis_Graphs;
      V_Final : Flow_Graphs.Vertex_Id)
      return Flow_Id_Sets.Set;
   --  Compute all inputs the given vertex depends on. For IPFA please use the
   --  function IPFA_Dependency, which also includes dependencies on called
   --  subprograms.
   --
   --  Complexity is O(N)

   function IPFA_Dependency
     (FA      : Flow_Analysis_Graphs;
      V_Final : Flow_Graphs.Vertex_Id)
      return Vertex_Sets.Set;
   pragma Unreferenced (IPFA_Dependency);
   --  Compute all inputs the given vertex depends on
   --
   --  Complexity is O(N)

   function Compute_Dependency_Relation
     (FA : Flow_Analysis_Graphs)
      return Dependency_Maps.Map;
   --  Computes the actual dependency relation of the given subprogram
   --
   --  Complexity is O(N^2)

   use type Common_Containers.Node_Sets.Set;  --  for the "or" operator

   procedure Compute_Globals
     (FA                    : Flow_Analysis_Graphs;
      Globals               : out Global_Nodes;
      Proof_Calls           : out Node_Sets.Set;
      Definite_Calls        : out Node_Sets.Set;
      Conditional_Calls     : out Node_Sets.Set;
      Local_Definite_Writes : out Node_Sets.Set)
   with Pre  => FA.Generating_Globals and FA.Is_Generative,
        Post => Definite_Calls.Intersection (Conditional_Calls).Is_Empty
                and then Proof_Calls.Intersection
                           (Definite_Calls or Conditional_Calls).Is_Empty
                and then Local_Definite_Writes.Is_Subset
                           (Of_Set => FA.GG.Local_Variables);
   --  Computes globals (and procedure calls) from the given graphs
   --  ??? this name has nothing to do with "computed globals" (aka Yannick's)
   --
   --  Complexity is O(N)
   --  @param FA are the flow graphs for which we compute globals
   --  @param Inputs_Proof are global variables read exclusively in proof
   --    contexts
   --  @param Inputs are global variables read (except for variables read in
   --    proof contexts)
   --  @param Outputs are global variables written (they may overlap with
   --    Inputs but not with Inputs_Proof)
   --  @param Proof_Calls are subprograms called exclusively in proof contexts
   --  @param Definite_Calls are subprograms definitely called
   --  @param Conditional_Calls are subprograms conditionally called
   --  @param Local_Variables are local variables (including formal paramaters)
   --  @param Local_Ghost_Variables are local ghost variables
   --  @param Local_Subprograms are nested subprograms
   --  @param Local_Definite_Writes are local variables that are definitely
   --    initialized after package elaboration.

end Flow.Slice;
