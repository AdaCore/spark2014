------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                        C H E C K E D _ T Y P E S                         --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                Copyright (C) 2016-2021, Altran UK Limited                --
--                     Copyright (C) 2016-2021, AdaCore                     --
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

--  This package contains wrapper types around some of the front-end types (in
--  particular Node_Id and Entity_Id) with predicates that enforce various
--  assumptions.

with Einfo.Entities; use Einfo.Entities;
with Sinfo.Nodes;    use Sinfo.Nodes;

package Checked_Types is

   -----------------
   -- Subprograms --
   -----------------

   --  In SPARK we also consider entries to be subprograms. We do not consider
   --  generics to be subprograms. We also exclude E_Operator here as we will
   --  never get this in SPARK (if the Expander works as intended).

   subtype Subprogram_Id is N_Entity_Id with
     Predicate => Ekind (Subprogram_Id) in E_Function
                                         | E_Procedure
                                         | Entry_Kind;

end Checked_Types;
