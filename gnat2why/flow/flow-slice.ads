------------------------------------------------------------------------------
--                                                                          --
--                           GNAT2WHY COMPONENTS                            --
--                                                                          --
--                           F L O W . S L I C E                            --
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

--  This package deals with computing slices (and thus dependency
--  relations).

package Flow.Slice is

   function Dependency
     (FA      : Flow_Analysis_Graphs;
      V_Final : Flow_Graphs.Vertex_Id)
      return Flow_Id_Sets.Set;
   --  Compute all inputs the given vertex depends on. For IPFA please
   --  use the function IPFA_Dependency, which also includes
   --  dependencies on called subprograms.
   --
   --  Complexity is O(N).

   function IPFA_Dependency
     (FA      : Flow_Analysis_Graphs;
      V_Final : Flow_Graphs.Vertex_Id)
      return Vertex_Sets.Set;
   --  Compute all inputs the given vertex depends on.
   --
   --  Complexity is O(N).

   function Compute_Dependency_Relation
     (FA : Flow_Analysis_Graphs)
      return Dependency_Maps.Map;
   --  Computes the actual dependency relation of the given
   --  subprogram.
   --
   --  Complexity is O(N^2)

   procedure Compute_Globals
     (FA                : Flow_Analysis_Graphs;
      Inputs_Proof      : out Node_Sets.Set;
      Inputs            : out Node_Sets.Set;
      Outputs           : out Node_Sets.Set;
      Proof_Calls       : out Node_Sets.Set;
      Definite_Calls    : out Node_Sets.Set;
      Conditional_Calls : out Node_Sets.Set;
      Local_Variables   : out Node_Sets.Set)
   with Pre => (FA.Compute_Globals and then
                  FA.Is_Generative and then
                  not FA.GG.Aborted),
        Post => (for all E of Definite_Calls =>
                   not Conditional_Calls.Contains (E)) and then
                (for all E of Proof_Calls =>
                   not (Definite_Calls.Contains (E) or
                          Conditional_Calls.Contains (E))) and then
                (for all E of Inputs_Proof =>
                   not (Inputs.Contains (E) or Outputs.Contains (E)));
   --  Computes the set of globals (and procedure calls) of the given
   --  subprogram.
   --
   --  Complexity is O(N)

end Flow.Slice;
