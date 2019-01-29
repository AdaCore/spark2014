------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                      X T R E E _ T R A V E R S A L                       --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                     Copyright (C) 2010-2019, AdaCore                     --
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

package Xtree_Traversal is
   --  This package provides generators for Why node accessors

   procedure Print_Traversal_Op_Declarations (O : in out Output_Record);
   --  Print kind-specific traversal operations

   procedure Print_Traverse_Body (O : in out Output_Record);
   --  Print a body implementing a recursive traversal of the Why syntax tree

   procedure Print_Traversal_Op_Stub_Declarations (O : in out Output_Record);
   --  Print stub declarations for traversal operations

   procedure Print_Traversal_Op_Stub_Bodies (O : in out Output_Record);
   --  Print bodies for traversal operations

   procedure Print_Treepr_Traversal_Op_Declarations (O : in out Output_Record);
   --  Print declarations of kind-specific traversal ops for tree printing

   procedure Print_Treepr_Traversal_Op_Bodies (O : in out Output_Record);
   --  Print bodies of traversal ops for tree printing

end Xtree_Traversal;
