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

with Ada.Containers;     use Ada.Containers;
with Why.Atree.Builders; use Why.Atree.Builders;
with Why.Gen.Names;      use Why.Gen.Names;

package body Why.Gen.Types is

   ---------------------------
   -- Declare_Abstract_Type --
   ---------------------------

   function New_Abstract_Type_Declaration (Name : String) return W_Type_Id is
      I : W_Identifier_Id;
      T : W_Type_Id;
   begin
      I := New_Identifier (Name);
      T := New_Type (Name => I);
      return T;
   end New_Abstract_Type_Declaration;

   -----------------------
   -- New_Abstract_Type --
   -----------------------

   function New_Abstract_Type (Name : String) return W_Abstract_Type_Id
   is
      I : constant W_Identifier_Id := New_Identifier (Name);
      T : constant W_Abstract_Type_Id := New_Abstract_Type (Name => I);
   begin
      return T;
   end New_Abstract_Type;

   -----------------------
   -- Declare_Enum_Type --
   -----------------------

   function New_Enum_Type_Declaration
     (Name         : String;
      Constructors : String_Lists.List) return W_Type_Id
   is
      use String_Lists;

      Len     : constant Count_Type :=
                  String_Lists.Length (Constructors);
      Constrs : W_Constr_Decl_Array (1 .. Integer (Len));
      Cursor  : String_Lists.Cursor := First (Constructors);
      Cnt     : Integer range 0 .. Integer (Len) := 0;
   begin
      if Len = 0 then
         return New_Abstract_Type_Declaration (Name);
      else
         while Has_Element (Cursor) loop
            Cnt := Cnt + 1;
            Constrs (Cnt) :=
              New_Constr_Decl (Name => New_Identifier (Element (Cursor)));
            Next (Cursor);
         end loop;
         return New_Type
           (Name => New_Identifier (Name),
            Definition => New_Adt_Definition (Constructors => Constrs));
      end if;
   end New_Enum_Type_Declaration;

end Why.Gen.Types;
