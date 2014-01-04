------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                        W H Y - G E N - D E C L                           --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                       Copyright (C) 2010-2014, AdaCore                   --
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
with Why.Atree.Mutators;  use Why.Atree.Mutators;
with Why.Gen.Names;       use Why.Gen.Names;
with Why.Sinfo;           use Why.Sinfo;
with Why.Types;           use Why.Types;

package body Why.Gen.Decl is

   ----------
   -- Emit --
   ----------

   procedure Emit
     (Theory : W_Theory_Declaration_Id;
      Decl : W_Declaration_Id) is
   begin
      Theory_Declaration_Append_To_Declarations
        (Id => Theory,
         New_Item => +Decl);
   end Emit;

   -------------------
   -- New_Type_Decl --
   -------------------

   function New_Type_Decl (Name : String) return W_Declaration_Id is
   begin
      return
        New_Type_Decl
          (Name   => New_Identifier (Name => Name),
           Labels => Name_Id_Sets.Empty_Set);
   end New_Type_Decl;

   function New_Type_Decl
     (Name  : W_Identifier_Id;
      Alias : W_Type_Id) return W_Declaration_Id is
   begin
      return New_Type_Decl
        (Name => Name,
         Labels => Name_Id_Sets.Empty_Set,
         Definition => New_Transparent_Type_Definition
           (Domain          => EW_Prog,
            Type_Definition => Alias));
   end New_Type_Decl;

end Why.Gen.Decl;
