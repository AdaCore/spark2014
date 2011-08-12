------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                        W H Y - G E N - T Y P E S                         --
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

with Ada.Containers;     use Ada.Containers;
with Why.Atree.Builders; use Why.Atree.Builders;
with Why.Gen.Decl;       use Why.Gen.Decl;
with Why.Gen.Names;      use Why.Gen.Names;

package body Why.Gen.Types is

   -------------------------------
   -- New_Enum_Type_Declaration --
   -------------------------------

   procedure New_Enum_Type_Declaration
     (File         : W_File_Id;
      Name         : String;
      Constructors : String_Lists.List)
   is
      use String_Lists;

      Len     : constant Count_Type :=
                  String_Lists.Length (Constructors);
      Constrs : W_Constr_Decl_Array (1 .. Integer (Len));
      Cursor  : String_Lists.Cursor := First (Constructors);
      Cnt     : Integer range 0 .. Integer (Len) := 0;
   begin
      if Len = 0 then
         Emit (File, New_Type (Name));

      else
         while Has_Element (Cursor) loop
            Cnt := Cnt + 1;
            Constrs (Cnt) :=
              New_Constr_Decl
                (Name => New_Identifier (Element (Cursor)));
            Next (Cursor);
         end loop;

         Emit
           (File,
            New_Adt_Definition
              (Name         => New_Identifier (Name),
               Constructors => Constrs));
      end if;
   end New_Enum_Type_Declaration;

end Why.Gen.Types;
