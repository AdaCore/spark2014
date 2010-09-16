------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                    G N A T 2 W H Y - S T A N D A R D                     --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                       Copyright (C) 2010, AdaCore                        --
--                                                                          --

-- gnat2why is  free  software;  you can redistribute it and/or modify it --
-- under terms of the  GNU General Public License as published  by the Free --
-- Software Foundation;  either version  2,  or  (at your option) any later --
-- version. gnat2why is distributed in the hope that it will  be  useful, --
-- but WITHOUT ANY WARRANTY; without even the implied warranty of MERCHAN-  --
-- TABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public --
-- License  for more details. You  should  have  received a copy of the GNU --
-- General Public License  distributed with GNAT; see file COPYING. If not, --
-- write to the Free Software Foundation,  51 Franklin Street, Fifth Floor, --
-- Boston,                                                                  --
--                                                                          --
-- gnat2why is maintained by AdaCore (http://www.adacore.com)             --
--                                                                          --
------------------------------------------------------------------------------

with Types;  use Types;
with Ttypes; use Ttypes;

with Outputs; use Outputs;

with Why.Ids;       use Why.Ids;
with Why.Gen.Enums; use Why.Gen.Enums;
with Why.Gen.Ints;  use Why.Gen.Ints;

with Why.Atree.Sprint;   use Why.Atree.Sprint;
with Why.Atree.Builders; use Why.Atree.Builders;

package body Gnat2Why.Standard is

   ---------------------
   -- Create_Standard --
   ---------------------

   procedure Create_Standard is
      File : constant W_File_Id := New_File;
   begin
      Declare_Abstract_Boolean_Type (File, "standard__boolean");

      Declare_Abstract_Signed_Int
        (File,
         "standard__integer",
         Standard_Integer_Size);
      Declare_Abstract_Signed_Int
        (File,
         "standard__natural",
         0,
         2 ** Natural (Standard_Integer_Size - 1) - 1);
      Declare_Abstract_Signed_Int
        (File,
         "standard__positive",
         1,
         2 ** Natural (Standard_Integer_Size - 1) - 1);
      Declare_Abstract_Signed_Int
        (File,
         "standard__short_short_integer",
         Standard_Short_Short_Integer_Size);
      Declare_Abstract_Signed_Int
        (File,
         "standard__short_integer",
         Standard_Short_Integer_Size);
      Declare_Abstract_Signed_Int
        (File,
         "standard__long_integer",
         Standard_Long_Integer_Size);
      Declare_Abstract_Signed_Int
        (File,
         "standard__long_long_integer",
         Standard_Long_Long_Integer_Size);

      Open_Current_File ("standard.why");
      Sprint_Why_Node (File, Current_File);
      Close_Current_File;
   end Create_Standard;

end Gnat2Why.Standard;
