------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                     W H Y - G E N - N A M E _ G E N                      --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                       Copyright (C) 2010-2011, AdaCore                   --
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

with Why.Atree.Builders;  use Why.Atree.Builders;
with Why.Atree.Accessors; use Why.Atree.Accessors;

package body Why.Gen.Name_Gen is

   --------
   -- Id --
   --------

   function Id
     (Ada_Node : Node_Id;
      Name     : String)
     return W_Identifier_Id
   is
      Sep_Prefix : constant String :=
                     (if Prefix /= "" then
                        Prefix & Separator
                      else
                        "");
      Sep_Suffix : constant String :=
                     (if Suffix /= "" then
                        Separator & Suffix
                      else
                        "");
      Result     : constant String :=
                     Sep_Prefix & Name & Sep_Suffix;
   begin
      Name_Len := 0;
      Add_Str_To_Name_Buffer (Result);
      return New_Identifier
        (Ada_Node => Ada_Node,
         Symbol   => Name_Find);
   end Id;

   --------
   -- Id --
   --------

   function Id
     (Ada_Node : Node_Id;
      Name     : Name_Id)
     return W_Identifier_Id is
   begin
      return Id (Ada_Node, Get_Name_String (Name));
   end Id;

   --------
   -- Id --
   --------

   function Id
     (Ada_Node : Node_Id;
      Name     : W_Identifier_Id)
     return W_Identifier_Id is
   begin
      return Id (Ada_Node, Identifier_Get_Symbol (Name));
   end Id;

   --------
   -- Id --
   --------

   function Id
     (Name : String)
     return W_Identifier_Id is
   begin
      return Id (Empty, Name);
   end Id;

   --------
   -- Id --
   --------

   function Id
     (Name : Name_Id)
     return W_Identifier_Id is
   begin
      return Id (Empty, Name);
   end Id;

   --------
   -- Id --
   --------

   function Id
     (Name : W_Identifier_Id)
     return W_Identifier_Id is
   begin
      return Id (Empty, Name);
   end Id;

end Why.Gen.Name_Gen;
