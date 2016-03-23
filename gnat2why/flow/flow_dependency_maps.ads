------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                   F L O W _ D E P E N D E N C Y _ M A P S                --
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

--  This package deals with parsing and representing dependency maps from the
--  depends and initializes aspects.

with Ada.Containers.Hashed_Maps;
with Atree;                      use Atree;
with Flow_Refinement;            use Flow_Refinement;
with Flow_Types;                 use Flow_Types;
with Sinfo;                      use Sinfo;
with Snames;                     use Snames;
with Sem_Util;                   use Sem_Util;
with Types;                      use Types;

package Flow_Dependency_Maps is

   ----------------------------------------------------------------------
   --  Types
   ----------------------------------------------------------------------

   package Dependency_Maps is new Ada.Containers.Hashed_Maps
     (Key_Type        => Flow_Id,
      Element_Type    => Flow_Id_Sets.Set,
      Hash            => Hash,
      Equivalent_Keys => "=",
      "="             => Flow_Id_Sets."=");

   ----------------------------------------------------------------------
   --  Functions
   ----------------------------------------------------------------------

   function Parse_Depends (N : Node_Id) return Dependency_Maps.Map
   with Pre => Nkind (N) = N_Pragma and then
               Get_Pragma_Id (N) in
                 Pragma_Depends         |
                 Pragma_Refined_Depends;

   function Parse_Initializes
     (N : Node_Id;
      P : Entity_Id;
      S : Flow_Scope)
      return Dependency_Maps.Map
   with Pre => (if Present (N) then
                  Nkind (N) = N_Pragma and then
                    Get_Pragma_Id (N) = Pragma_Initializes);
   --  Parses the Initializes aspect. If the initializes aspect does not exist
   --  but we have a generated initializes aspect then we use that.
   --
   --  When we parse the Initializes aspect we add any external state
   --  abstractions with the property Async_Writers set to the
   --  dependency map (even if the user did not manually write them
   --  there). This is to ensure that constituents that are not
   --  volatile and have Async_Writers are also initialized. Notice
   --  that as a result of this, the function may return a Dependency
   --  map even if there is no Initializes aspect to begin with. P
   --  represents the enclosing package.
   --  @param N is the node representing the initializes aspect
   --  @param P is the entity representing the package
   --  @param S is the Flow_Scope at which we need to up project the results
   --  @returns the dependency map representing the initializes aspect

   function Parse_Refined_State (N : Node_Id) return Dependency_Maps.Map
   with Pre => Nkind (N) = N_Pragma and then
               Get_Pragma_Id (N) = Pragma_Refined_State;

   --  Parses the Refined_State aspect

end Flow_Dependency_Maps;
