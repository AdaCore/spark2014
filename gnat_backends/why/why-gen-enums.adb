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
with Why.Gen.Types;      use Why.Gen.Types;
with Why.Gen.Names;      use Why.Gen.Names;
with Why.Unchecked_Ids;  use Why.Unchecked_Ids;

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

   procedure Declare_Enum_Type (
      File         : W_File_Id;
      Name         : String;
      Constructors : String_Lists.List)
   is
      use String_Lists;
      T_I    : constant W_Identifier_Id               := New_Identifier (Name);
      Adt    : constant W_Adt_Definition_Unchecked_Id :=
         New_Unchecked_Adt_Definition;
      T      : constant W_Type_Unchecked_Id           := New_Unchecked_Type;
      Cursor : String_Lists.Cursor                    := First (Constructors);
      C_I : W_Identifier_Id;
      D : W_Constr_Decl_Unchecked_Id;
      --  ??? Not fully implemented yet
   begin
      while Has_Element (Cursor) loop
         C_I := New_Identifier (Element (Cursor));
         D := New_Unchecked_Constr_Decl;
         Constr_Decl_Set_Name (D, C_I);
         Adt_Definition_Append_To_Constructors (Adt, D);
         Next (Cursor);
      end loop;
      Type_Set_Name (T, T_I);
      Type_Set_Definition (T, Adt);
      File_Append_To_Declarations (File, New_Logic_Declaration (Decl => T));
   end Declare_Enum_Type;

end Why.Gen.Enums;
