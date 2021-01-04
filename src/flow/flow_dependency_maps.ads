------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                   F L O W _ D E P E N D E N C Y _ M A P S                --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                Copyright (C) 2013-2021, Altran UK Limited                --
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
with Einfo;                      use Einfo;
with Flow_Types;                 use Flow_Types;
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
   with Pre => Get_Pragma_Id (N) in Pragma_Depends | Pragma_Refined_Depends;

   function Parse_Initializes
     (P    : Entity_Id;
      Scop : Flow_Scope)
      return Dependency_Maps.Map
   with Pre  => Ekind (P) = E_Package,
        Post => (for all C in Parse_Initializes'Result.Iterate =>
                    Dependency_Maps.Key (C).Kind in Direct_Mapping
                                                  | Magic_String
                                                  | Null_Value);
   --  Parse the Initializes aspect if it exists, or a generated one otherwise
   --
   --  When we parse the Initializes aspect we add any external state
   --  abstractions with enabled property Async_Writers to the dependency map
   --  (even if the user did not manually put them there). This ensures that
   --  constituents that are not volatile but have Async_Writers are also
   --  initialized. In effect, we may return a Dependency map even if there
   --  is no Initializes aspect to begin with.
   --
   --  @param P package entity
   --  @param Scop is the Flow_Scope at which we need to up project the results
   --  @returns the dependency map representing the initializes aspect

end Flow_Dependency_Maps;
