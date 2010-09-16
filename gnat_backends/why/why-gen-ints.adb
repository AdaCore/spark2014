------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                         W H Y - G E N - I N T S                          --
--                                                                          --
--                                 S p e c                                  --
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

with Why.Atree.Mutators; use Why.Atree.Mutators;
with Why.Gen.Types;      use Why.Gen.Types;

package body Why.Gen.Ints is

   ---------------------------------
   -- Declare_Abstract_Signed_Int --
   ---------------------------------

   procedure Declare_Abstract_Signed_Int
     (File : W_File_Id;
      Name : String;
      Size : Pos) is
   begin
      Declare_Abstract_Signed_Int (File,
                                   Name,
                                   -2 ** Natural (Size - 1),
                                   2 ** Natural (Size - 1)  - 1);
   end Declare_Abstract_Signed_Int;

   procedure Declare_Abstract_Signed_Int
     (File  : W_File_Id;
      Name  : String;
      First : Int;
      Last  : Int)
   is
      pragma Unreferenced (First);
      pragma Unreferenced (Last);
      --  ??? Not fully implemented yet
      T : constant W_Type_Id := Declare_Abstract_Type (Name);
   begin
      File_Append_To_Declarations (File, T);
   end Declare_Abstract_Signed_Int;

end Why.Gen.Ints;
