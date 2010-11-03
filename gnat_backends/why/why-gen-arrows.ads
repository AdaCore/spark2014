------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                       W H Y - G E N - A R R O W S                        --
--                                                                          --
--                                 S p e c                                  --
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

with Why.Types;            use Why.Types;
with Why.Ids;              use Why.Ids;
with Why.Unchecked_Ids;    use Why.Unchecked_Ids;
with Why.Atree.Properties; use Why.Atree.Properties;

package Why.Gen.Arrows is
   --  This package provides ways to create arrow types

   function New_Arrow_Stack
     (Return_Type : W_Primitive_Type_Id)
     return W_Arrow_Type_Unchecked_Id with
     Pre => (Is_Root (Return_Type));
   --  This creates an invalid arrow type where only the return type
   --  (the right hand side of the arrow) is specified. The left hand
   --  side is left empty. Push_Arg should then be used to complete the
   --  the subprogram spec that this arrow express, by adding parameters
   --  (last one being push first).

   function Push_Arg
     (Arrow    : W_Arrow_Type_Unchecked_Id;
      Name     : W_Identifier_OId := Why_Empty;
      Arg_Type : W_Simple_Value_Type_Id)
     return W_Arrow_Type_Id with
     Pre => (Is_Root (Name)
             and then Is_Root (Arg_Type));
   --  Preprend the given parameters in Arrow, i.e. generating something
   --  like "Name : Arg_Type -> Arrow".

   function Get_Computation_Spec
     (Arrow : W_Arrow_Type_Id)
     return W_Computation_Spec_Id;
   --  Return the computation spec that is at the end of an arrow chain.
   --  e.g. from:
   --
   --     n1 : type1 -> n2 : type2 -> {pre} type3 {post}
   --
   --  return:
   --
   --     {pre} type 3 {post}

end Why.Gen.Arrows;
