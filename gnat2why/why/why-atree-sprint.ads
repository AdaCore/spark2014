------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                     W H Y - A T R E E - S P R I N T                      --
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

with Outputs;          use Outputs;
with Why.Atree.Tables; use Why.Atree.Tables;
with Gnat2Why.Util;    use Gnat2Why.Util;

package Why.Atree.Sprint is

   --  This package provides ways to print source code from the abstract
   --  syntax tree.

   procedure Sprint_Why_Node
     (Node : Why_Node_Id; To : Output_Id := Stdout) with
     Pre => (Get_Kind (Node) /= W_Unused_At_Start);
   --  Generate why code for Node and send it to Output_Id.

   procedure Print_Section
     (WF : Why_Section; To : Output_Id := Stdout);

   procedure Print_Modules_List
     (L : Why_Node_Lists.List; To : Output_Id);
   --  Print a list of modules

   procedure wpg (Node : Why_Node_Id);
   pragma Export (Ada, wpg);
   --  Print generated source for argument Node. Intended only for use
   --  from gdb for debugging purposes.

end Why.Atree.Sprint;
