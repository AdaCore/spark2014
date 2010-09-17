------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                       W H Y - G E N - A R R O W S                        --
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

with Why.Atree.Builders;  use Why.Atree.Builders;
with Why.Atree.Mutators;  use Why.Atree.Mutators;
with Why.Atree.Accessors; use Why.Atree.Accessors;

package body Why.Gen.Arrows is

   ---------------------
   -- New_Arrow_Stack --
   ---------------------

   function New_Arrow_Stack
     (Return_Type : W_Primitive_Type_Id)
     return W_Arrow_Type_Unchecked_Id
   is
      Contract   : constant W_Computation_Spec_Id :=
                     New_Computation_Spec (Return_Type => Return_Type,
                                           Effects => New_Effects);
      Result     : constant W_Arrow_Type_Unchecked_Id :=
                     New_Unchecked_Arrow_Type;
   begin
      Arrow_Type_Set_Right (Result, Contract);
      return Result;
   end New_Arrow_Stack;

   --------------
   -- Push_Arg --
   --------------

   function Push_Arg
     (Arrow    : W_Arrow_Type_Unchecked_Id;
      Name     : W_Identifier_OId := Why_Empty;
      Arg_Type : W_Simple_Value_Type_Id)
     return W_Arrow_Type_Id
   is
      Left : constant W_Simple_Value_Type_Unchecked_Id :=
               Arrow_Type_Get_Left (Arrow);
   begin
      if Left = Why_Empty then
         Arrow_Type_Set_Left (Arrow, Arg_Type);
         Arrow_Type_Set_Name (Arrow, Name);
         return Arrow;
      else
         declare
            Result : constant W_Arrow_Type_Id :=
                       New_Arrow_Type (Name => Name,
                                       Left => Arg_Type,
                                       Right => Arrow);
         begin
            return Result;
         end;
      end if;

      pragma Assert (False);
      return Why_Empty;
   end Push_Arg;

end Why.Gen.Arrows;
