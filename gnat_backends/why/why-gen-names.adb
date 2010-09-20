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

with Why.Atree.Builders;  use Why.Atree.Builders;
with Why.Atree.Accessors; use Why.Atree.Accessors;
with Why.Atree.Mutators;  use Why.Atree.Mutators;

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

   ------------------
   -- Safe_Version --
   ------------------

   function Safe_Version (Name : W_Identifier_Id) return W_Identifier_Id is
      Prefix : constant String := "safe___";
      N_Id   : constant Name_Id := Identifier_Get_Symbol (Name);
      Img    : constant String := Get_Name_String (N_Id);
   begin
      return New_Identifier (Prefix & Img);
   end Safe_Version;

   --------------
   -- Set_Name --
   --------------

   procedure Set_Name (Id : W_Identifier_Id; Name : String) is
   begin
      Name_Len := 0;
      Add_Str_To_Name_Buffer (Name);
      Identifier_Set_Symbol (Id, Name_Find);
   end Set_Name;

   ----------------------
   -- To_Program_Space --
   ----------------------

   function To_Program_Space (Name : W_Identifier_Id) return W_Identifier_Id is
      Suffix : constant String := "_";
      N_Id   : constant Name_Id := Identifier_Get_Symbol (Name);
      Img    : constant String := Get_Name_String (N_Id);
   begin
      return New_Identifier (Img & Suffix);
   end To_Program_Space;

end Why.Gen.Names;
