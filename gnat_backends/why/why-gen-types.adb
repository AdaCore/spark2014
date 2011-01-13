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

with Why.Atree.Builders; use Why.Atree.Builders;
with Why.Atree.Mutators; use Why.Atree.Mutators;
with Why.Gen.Names;      use Why.Gen.Names;
with Why.Unchecked_Ids;  use Why.Unchecked_Ids;

package body Why.Gen.Types is

   ---------------------------
   -- Declare_Abstract_Type --
   ---------------------------

   function Declare_Abstract_Type (Name : String) return W_Type_Id is
      I : W_Identifier_Id;
      T : W_Type_Id;
   begin
      I := New_Identifier (Name);
      T := New_Type (Name => I);
      return T;
   end Declare_Abstract_Type;

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

   function Declare_Enum_Type
     (Name         : String;
      Constructors : String_Lists.List) return W_Type_Id
   is
      use String_Lists;

      T_I    : constant W_Identifier_Id := New_Identifier (Name);
      Adt    : constant W_Adt_Definition_Unchecked_Id :=
                 New_Unchecked_Adt_Definition;
      T      : constant W_Type_Unchecked_Id := New_Unchecked_Type;
      Cursor : String_Lists.Cursor := First (Constructors);
   begin
      Type_Set_Name (T, T_I);
      while Has_Element (Cursor) loop
         declare
            C_I : constant W_Identifier_Id :=
                    New_Identifier (Element (Cursor));
            D   : constant W_Constr_Decl_Unchecked_Id :=
                    New_Constr_Decl (Name => C_I);
         begin
            Adt_Definition_Append_To_Constructors (Adt, D);
            Next (Cursor);
         end;
      end loop;
      Type_Set_Definition (T, Adt);
      return T;
   end Declare_Enum_Type;

end Why.Gen.Types;
