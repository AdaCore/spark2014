------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                        W H Y - G E N - E N U M S                         --
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

with Why.Atree.Builders; use Why.Atree.Builders;
with Why.Atree.Mutators; use Why.Atree.Mutators;

package body Why.Gen.Enums is

   -----------------------------------
   -- Declare_Abstract_Boolean_Type --
   -----------------------------------

   procedure Declare_Abstract_Boolean_Type (File : W_File_Id; Name : String)
   is
      T : constant W_Type_Id := Declare_Abstract_Type (Name);
      --  ??? Not fully implemented yet
   begin
      File_Append_To_Declarations (File, New_Logic_Declaration (Decl => T));
   end Declare_Abstract_Boolean_Type;

   procedure Declare_Enum_Type
     (File         : W_File_Id;
      Name         : String;
      Constructors : String_Lists.List)
   is
      --  ??? Not fully implemented yet
   begin
      File_Append_To_Declarations
        (File,
         New_Logic_Declaration
         (Decl => Declare_Enum_Type (Name, Constructors)));
   end Declare_Enum_Type;

end Why.Gen.Enums;
