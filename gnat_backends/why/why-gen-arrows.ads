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

with Why.Types;         use Why.Types;
with Why.Ids;           use Why.Ids;
with Why.Unchecked_Ids; use Why.Unchecked_Ids;

package Why.Gen.Arrows is

   function New_Arrow_Stack
     (Return_Type : W_Primitive_Type_Id)
     return W_Arrow_Type_Unchecked_Id;

   function Push_Arg
     (Arrow    : W_Arrow_Type_Unchecked_Id;
      Name     : W_Identifier_OId := Why_Empty;
      Arg_Type : W_Simple_Value_Type_Id)
     return W_Arrow_Type_Id;

end Why.Gen.Arrows;
