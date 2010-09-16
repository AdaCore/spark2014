------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                        W H Y - G E N - N A M E S                         --
--                                                                          --
--                                 B o d y                                  --
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

with Namet; use Namet;

with Why.Atree.Builders; use Why.Atree.Builders;

package body Why.Gen.Names is

   ---------------------------
   -- New_Conversion_To_Int --
   ---------------------------

   function New_Conversion_To_Int (Name : String) return W_Identifier_Id is
      Prefix : constant String := "integer_of___";
   begin
      return New_Identifier (Prefix & Name);
   end New_Conversion_To_Int;

   --------------------
   -- New_Identifier --
   --------------------

   function New_Identifier (Name : String) return W_Identifier_Id is
   begin
      Name_Len := 0;
      Add_Str_To_Name_Buffer (Name);
      return New_Identifier (Symbol => Name_Find);
   end New_Identifier;

end Why.Gen.Names;
