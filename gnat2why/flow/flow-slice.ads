------------------------------------------------------------------------------
--                                                                          --
--                           GNAT2WHY COMPONENTS                            --
--                                                                          --
--                           F L O W . S L I C E                            --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                  Copyright (C) 2013-2016, Altran UK Limited              --
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
   --  Compute all inputs the given vertex depends on. For IPFA please
   --  use the function IPFA_Dependency, which also includes
   --  dependencies on called subprograms.
   --
   --  Complexity is O(N)

   function IPFA_Dependency
     (FA      : Flow_Analysis_Graphs;
      V_Final : Flow_Graphs.Vertex_Id)
      return Vertex_Sets.Set;
   --  Compute all inputs the given vertex depends on.
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
      Inputs_Proof          : out Node_Sets.Set;
      Inputs                : out Node_Sets.Set;
      Outputs               : out Node_Sets.Set;
      Proof_Calls           : out Node_Sets.Set;
      Definite_Calls        : out Node_Sets.Set;
      Conditional_Calls     : out Node_Sets.Set;
      Local_Variables       : out Node_Sets.Set;
      Local_Subprograms     : out Node_Sets.Set;
      Local_Definite_Writes : out Node_Sets.Set)
   with Pre  => (FA.Generating_Globals and then
                   FA.Is_Generative and then
                   not FA.GG.Aborted),
        Post => Definite_Calls.Intersection (Conditional_Calls).Is_Empty
                and then Proof_Calls.Intersection
                           (Definite_Calls or Conditional_Calls).Is_Empty
                and then Inputs_Proof.Intersection
                           (Inputs or Outputs).Is_Empty;
   --  Computes the set of globals (and procedure calls) of the given
   --  subprogram.
   --
   --  Complexity is O(N)
   --  @param FA is the flow graph for which we compute globals
   --  @param Inputs_Proof is the set of global variables read exclusively
   --    in proof contexts
   --  @param Inputs is the set global variables read (does not include
   --    variables read in proof contexts)
   --  @param Outputs is the set of global variables written (there can
   --    be an overlap with the Input but not with the Input_Proof)
   --  @param Proof_Calls is the set of subprograms called exclusively
   --    in proof contexts
   --  @param Definite_Calls is the set of subprograms definitely called
   --  @param Conditionl_Calls is the set of subprograms conditionally
   --    called
   --  @param Local_Variables is the set of local variables (this set
   --    also contains formal paramaters)
   --  @param Local_Subprograms is the set of all nested subprograms
   --  @param Local_Definite_Writes is the set of all local variables that
   --     are definitely initialized once the package has been elaborated.

end Flow.Slice;
