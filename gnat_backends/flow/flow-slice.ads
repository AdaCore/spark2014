------------------------------------------------------------------------------
--                                                                          --
--                           GNAT2WHY COMPONENTS                            --
--                                                                          --
--                           F L O W . S L I C E                            --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                  Copyright (C) 2013, Altran UK Limited                   --
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

end Flow.Slice;
