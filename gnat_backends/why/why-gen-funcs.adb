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

with Why.Sinfo;           use Why.Sinfo;
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
     (File   : W_File_Id;
      Name   : W_Identifier_Id;
      Arrows : W_Arrow_Type_Id)
   is
      Logic : constant W_Logic_Unchecked_Id := New_Unchecked_Logic;
      Spec  : constant W_Logic_Type_Unchecked_Id :=
                New_Unchecked_Logic_Type;

      procedure Append_To_Spec (Arrow : W_Arrow_Type_Id);
      --  Append the content of Arrow in the declaration of the
      --  logic function; in other words, build a logic spec from
      --  a program spec. e.g. transform:
      --
      --  x : type1 -> y : type2 -> {} type3 {}
      --
      --  ...into:
      --
      --  type1, type2 -> type3

      --------------------
      -- Append_To_Spec --
      --------------------

      procedure Append_To_Spec (Arrow : W_Arrow_Type_Id) is
         Right : constant W_Computation_Type_Id :=
                   Arrow_Type_Get_Right (Arrow);
      begin
         Logic_Type_Append_To_Arg_Types
           (Spec,
            Duplicate_Logic_Arg_Type (Id => Arrow_Type_Get_Left (Arrow)));

         if Get_Kind (Right) = W_Computation_Spec then
            Logic_Type_Set_Return_Type
              (Spec,
               Duplicate_Logic_Return_Type
               (Id => Computation_Spec_Get_Return_Type (Right)));
         else
            Append_To_Spec (Right);
         end if;
      end Append_To_Spec;

   --  Start of processing for Declare_Logic

   begin
      Append_To_Spec (Arrows);
      Logic_Append_To_Names (Logic, Name);
      Logic_Set_Logic_Type (Logic, Spec);
      File_Append_To_Declarations (File,
                                   New_Logic_Declaration (Decl => Logic));
   end Declare_Logic;

   ----------------------------------
   -- Declare_Logic_And_Parameters --
   ----------------------------------

   procedure Declare_Logic_And_Parameters
     (File   : W_File_Id;
      Name   : W_Identifier_Id;
      Arrows : W_Arrow_Type_Id) is
   begin
      Declare_Logic (File, Name, Arrows);
      Declare_Parameter (File, To_Program_Space (Name), Arrows);
   end Declare_Logic_And_Parameters;

   -----------------------
   -- Declare_Parameter --
   -----------------------

   procedure Declare_Parameter
     (File   : W_File_Id;
      Name   : W_Identifier_Id;
      Arrows : W_Arrow_Type_Id)
   is
      Parameter : constant W_Parameter_Declaration_Unchecked_Id :=
                    New_Unchecked_Parameter_Declaration;
   begin
      Parameter_Declaration_Append_To_Names (Parameter, Name);
      Parameter_Declaration_Set_Parameter_Type (Parameter, Arrows);
      File_Append_To_Declarations (File, Parameter);
   end Declare_Parameter;

end Why.Gen.Funcs;
