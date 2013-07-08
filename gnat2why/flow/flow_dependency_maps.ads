------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                   F L O W _ D E P E N D E N C Y _ M A P S                --
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

--  This package deals with parsing and representing dependency maps
--  from the depends and initializes aspects.

with Ada.Containers.Hashed_Maps;

with Types;      use Types;

with Flow_Types; use Flow_Types;

package Flow_Dependency_Maps is

   ----------------------------------------------------------------------
   --  Types
   ----------------------------------------------------------------------

   type Optional_Flow_Id_Set (Exists : Boolean := False) is record
      case Exists is
         when True =>
            The_Set : Flow_Id_Sets.Set;

         when False =>
            null;
      end case;
   end record;

   package Optional_Dependency_Maps is new Ada.Containers.Hashed_Maps
     (Key_Type        => Flow_Id,
      Element_Type    => Optional_Flow_Id_Set,
      Hash            => Hash,
      Equivalent_Keys => "=",
      "="             => "=");
   --  This is like a dependency map, but we can distinguish between
   --  the "a => null" and "a" case.

   package Dependency_Maps is new Ada.Containers.Hashed_Maps
     (Key_Type        => Flow_Id,
      Element_Type    => Flow_Id_Sets.Set,
      Hash            => Hash,
      Equivalent_Keys => "=",
      "="             => Flow_Id_Sets."=");

   ----------------------------------------------------------------------
   --  Functions
   ----------------------------------------------------------------------

   function Parse_Depends (N : Node_Id)
                           return Dependency_Maps.Map;

   function Parse_Initializes (N : Node_Id)
                               return Optional_Dependency_Maps.Map;

end Flow_Dependency_Maps;
