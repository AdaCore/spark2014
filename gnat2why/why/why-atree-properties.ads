------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                 W H Y - A T R E E - P R O P E R T I E S                  --
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

with Why.Atree.Tables; use Why.Atree.Tables;

package Why.Atree.Properties with Ghost is

   function Is_Root (Node_Id : Why_Node_Id) return Boolean;
   function Is_Root (List_Id : Why_Node_List) return Boolean;
   --  True if the given node has no father

private

   function Is_Root (Node_Id : Why_Node_Id) return Boolean is
      (Get_Link (Node_Id) = Why_Empty);

   function Is_Root (List_Id : Why_Node_List) return Boolean is
      (Get_Link (List_Id) = Why_Empty);

end Why.Atree.Properties;
