------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                            W H Y - T Y P E S                             --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                       Copyright (C) 2010-2017, AdaCore                   --
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

with Common_Containers; use Common_Containers;

package Why.Types is

   --  This package hierarchy provides basic types for Why syntax trees

   type Why_Int is range -2 ** 31 .. +2 ** 31 - 1;

   type Why_Node_Set is new Why_Int range 0 .. Why_Int'Last;

   type Why_Node_Id is new Why_Node_Set range 0 .. Why_Node_Set'Last / 2;

   type Why_Node_List is new Why_Node_Set
     range Why_Node_Set (Why_Node_Id'Last + 1) .. Why_Node_Set'Last;

   Why_Empty : constant := 0;

   function No (N : Why_Node_Id) return Boolean is (N = Why_Empty);
   --  Returns True if N is the empty node, False otherwise

   function Present (N : Why_Node_Id) return Boolean is (N /= Why_Empty);
   --  Returns True if N is not the empty node, False otherwise

   subtype Name_Id_Set is Name_Id_Sets.Set;

end Why.Types;
