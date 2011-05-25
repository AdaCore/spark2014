------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                             W H Y - I N T E R                            --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                       Copyright (C) 2010-2011, AdaCore                   --
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

package body Why.Inter is

   ---------------------
   -- Add_With_Clause --
   ---------------------

   procedure Add_With_Clause (P : out Why_Package; Name : String) is
   begin
      P.WP_Context.Append (Name);
   end Add_With_Clause;

   procedure Add_With_Clause (P : out Why_Package; Other : Why_Package) is
   begin
      P.WP_Context.Append (Other.WP_Name.all);
   end Add_With_Clause;

   -------------------------
   -- Make_Empty_Why_Pack --
   -------------------------

   function Make_Empty_Why_Pack (S : String) return Why_Package
   is
   begin
      return
        (WP_Name    => new String'(S),
         WP_Context => String_Lists.Empty_List,
         WP_Decls   => List_Of_Nodes.Empty_List);
   end Make_Empty_Why_Pack;

end Why.Inter;
