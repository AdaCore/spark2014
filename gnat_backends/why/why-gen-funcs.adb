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

with Why.Gen.Names;       use Why.Gen.Names;

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
      File_Append_To_Declarations (File,
                                   New_Logic_Declaration (Decl => Logic));
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
      Declare_Parameter (File, To_Program_Space (Name), Binders, Return_Type);
   end Declare_Logic_And_Parameters;

   -----------------------
   -- Declare_Parameter --
   -----------------------

   procedure Declare_Parameter
     (File        : W_File_Id;
      Name        : W_Identifier_Id;
      Binders     : W_Binders_Id;
      Return_Type : W_Primitive_Type_Id)
   is
      Parameter  : constant W_Parameter_Declaration_Unchecked_Id :=
                     New_Unchecked_Parameter_Declaration;
      Contract   : constant W_Computation_Spec_Id :=
                     New_Computation_Spec (Return_Type => Return_Type,
                                           Effects => New_Effects);
      --  ??? This is not correct. The left part of an arrow cannot
      --  be of kind Binders; only fully specified programs
      --  have W_Binders nodes... Parameters should use a chain
      --  of W_Computation_Type nodes.
      Arrow      : constant W_Anonymous_Arrow_Type_Id :=
                     New_Anonymous_Arrow_Type (Left => Binders,
                                               Right => Contract);
   begin
      Parameter_Declaration_Append_To_Names (Parameter, Name);
      Parameter_Declaration_Set_Parameter_Type (Parameter, Arrow);
      File_Append_To_Declarations (File, Parameter);
   end Declare_Parameter;

end Why.Gen.Funcs;
