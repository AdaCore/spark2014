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

with Outputs; use Outputs;

with Why.Ids;       use Why.Ids;
with Why.Gen.Types; use Why.Gen.Types;

with Why.Atree.Sprint;   use Why.Atree.Sprint;
with Why.Atree.Mutators; use Why.Atree.Mutators;
with Why.Atree.Builders; use Why.Atree.Builders;

package body Gnat2Why.Standard is

   ---------------------
   -- Create_Standard --
   ---------------------

   procedure Create_Standard is
      F : constant W_File_Id := New_File;
   begin
      File_Append_To_Declarations
        (F, Declare_Abstract_Type ("standard__boolean"));
      File_Append_To_Declarations
        (F, Declare_Abstract_Type ("standard__integer"));
      File_Append_To_Declarations
        (F, Declare_Abstract_Type ("standard__natural"));
      File_Append_To_Declarations
        (F, Declare_Abstract_Type ("standard__positive"));
      Open_Current_File ("standard.why");
      Sprint_Why_Node (F, Current_File);
      Close_Current_File;
   end Create_Standard;

end Gnat2Why.Standard;
