------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                        W H Y - G E N - F U N C S                         --
--                                                                          --
--                                 B o d y                                  --
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

with Why.Unchecked_Ids;   use Why.Unchecked_Ids;
with Why.Atree.Builders;  use Why.Atree.Builders;
with Why.Atree.Mutators;  use Why.Atree.Mutators;
with Why.Atree.Accessors; use Why.Atree.Accessors;
with Why.Atree.Tables;    use Why.Atree.Tables;

package body Why.Gen.Funcs is

   -------------------
   -- Declare_Logic --
   -------------------

   procedure Declare_Logic
     (File        : W_File_Id;
      Name        : W_Identifier_Id;
      Binders     : W_Binders_Id;
      Return_Type : W_Logic_Return_Type_Id)
   is
      use Node_Lists;

      Logic     : constant W_Logic_Unchecked_Id := New_Unchecked_Logic;
      Spec      : constant W_Logic_Type_Unchecked_Id :=
                    New_Unchecked_Logic_Type;
      Bind_List : constant List := Get_List (Binders_Get_Binders (Binders));
      Position  : Cursor := First (Bind_List);
   begin
      Logic_Type_Set_Return_Type (Spec, Return_Type);

      while Position /= No_Element loop
         declare
            Binder   : constant W_Binder_Id := Element (Position);
            Arg_Type : constant W_Logic_Arg_Type_Unchecked_Id :=
                         Binder_Get_Arg_Type (Binder);
         begin
            Logic_Type_Append_To_Arg_Types (Spec, Arg_Type);
         end;

         Next (Position);
      end loop;

      Logic_Append_To_Names (Logic, Name);
      Logic_Set_Logic_Type (Logic, Spec);
      File_Append_To_Declarations (File, Logic);
   end Declare_Logic;

   ----------------------------------
   -- Declare_Logic_And_Parameters --
   ----------------------------------

   procedure Declare_Logic_And_Parameters
     (File        : W_File_Id;
      Name        : W_Identifier_Id;
      Binders     : W_Binders_Id;
      Return_Type : W_Primitive_Type_Id) is
   begin
      Declare_Logic (File, Name, Binders, Return_Type);
      --  ??? Partially implemented
   end Declare_Logic_And_Parameters;

end Why.Gen.Funcs;
