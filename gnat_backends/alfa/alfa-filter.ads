------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                           A L F A . F I L T E R                          --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                        Copyright (C) 2011, AdaCore                       --
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
-- gnat2why is maintained by AdaCore (http://www.adacore.com)               --
--                                                                          --
------------------------------------------------------------------------------

with Why.Inter; use Why.Inter;

package Alfa.Filter is

   Alfa_Compilation_Units : List_Of_Why_Packs.List;

   procedure Filter_Compilation_Unit (N : Node_Id);
   --  Filter declarations in compilation unit N and generate compilation units
   --  which are appended to Compilation_Units.

   function Filter_Standard_Package return List_Of_Nodes.List;
   --  Return declarations of standard package that are in Alfa

   function Filter_Out_Standard_Package return List_Of_Nodes.List;
   --  Return entities of standard package that are not in Alfa

end Alfa.Filter;
