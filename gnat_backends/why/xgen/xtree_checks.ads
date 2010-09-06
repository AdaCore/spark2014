------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                         X T R E E _ C H E C K S                          --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                       Copyright (C) 2010, AdaCore                        --
--                                                                          --
-- gnat2why is  free  software;  you can redistribute it and/or modify it   --
-- under terms of the  GNU General Public License as published  by the Free --
-- Software Foundation;  either version  2,  or  (at your option) any later --
-- version. gnat2why is distributed in the hope that it will  be  useful,   --
-- but WITHOUT ANY WARRANTY; without even the implied warranty of MERCHAN-  --
-- TABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public --
-- License  for more details. You  should  have  received a copy of the GNU --
-- General Public License  distributed with GNAT; see file COPYING. If not, --
-- write to the Free Software Foundation,  51 Franklin Street, Fifth Floor, --
-- Boston,                                                                  --
--                                                                          --
-- gnat2why is maintained by AdaCore (http://www.adacore.com)               --
--                                                                          --
------------------------------------------------------------------------------

with Outputs; use Outputs;

package Xtree_Checks is
   --  This package provides routines to print tree-validity checks

   procedure Print_Checks_Declarations (O : in out Output_Record);
   --  Print tree-validity check declarations

   procedure Print_Checks_Bodies (O : in out Output_Record);
   --  Print tree-validity check bodies

   procedure Print_Cache_Checks_Declarations (O : in out Output_Record);
   --  Print declarations of cache accesses to tree-validity check

   procedure Print_Cache_Checks_Bodies (O : in out Output_Record);
   --  Print  bodies of cache access to tree-validity check

end Xtree_Checks;
