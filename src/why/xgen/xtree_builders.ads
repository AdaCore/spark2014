------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                       X T R E E _ B U I L D E R S                        --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                     Copyright (C) 2010-2020, AdaCore                     --
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

with Outputs; use Outputs;

package Xtree_Builders is
   --  This package provides generators for Why node builders

   procedure Print_Class_Wide_Builder_Declarations (O : in out Output_Record);
   --  Print builder declarations for class-wide ids

   procedure Print_Class_Wide_Builder_Bodies (O : in out Output_Record);
   --  Print builder bodies for class-wide ids

   procedure Print_Unchecked_Builder_Declarations (O : in out Output_Record);
   --  Print builder declarations for unchecked Why nodes

   procedure Print_Unchecked_Builder_Bodies (O : in out Output_Record);
   --  Print builder bodies for unchecked Why nodes

   Checked_Default_Value : constant String := "Is_Checked";
   --  Name of the constant used to initialize the field Checked. The
   --  initialization depends on the kind of constructor that we are
   --  executing; this dependancy is encapsulated into a local variable
   --  whose name is Checked_Default_Value.

end Xtree_Builders;
