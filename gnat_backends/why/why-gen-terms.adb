------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                   G N A T 2 W H Y - G E N - T E R M S                    --
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
with Why.Gen.Names;      use Why.Gen.Names;
with Why.Atree.Tables;   use Why.Atree.Tables;

package body Why.Gen.Terms is

   --------------
   -- New_Andb --
   --------------

   function New_Andb (Left, Right : W_Term_Id) return W_Term_Id
   is
   begin
      case Get_Kind (Left) is
         when W_True_Literal =>
            return Right;

         when others =>
            case Get_Kind (Right) is
               when W_True_Literal =>
                  return Left;

               when others =>
                  return
                     New_Operation
                        (Name       => New_Identifier ("bool_and"),
                         Parameters => (1 => Left, 2 => Right));
            end case;

      end case;
   end New_Andb;

   ---------------------
   -- New_Boolean_Cmp --
   ---------------------

   function New_Boolean_Cmp (Cmp : W_Relation; Left, Right : W_Term_Id)
      return W_Term_Id
   is
   begin
      return
         New_Operation
           (Name => New_Bool_Int_Cmp (Cmp),
            Parameters => (1 => Left, 2 => Right));

   end New_Boolean_Cmp;

   -------------
   -- New_Ifb --
   -------------

   function New_Ifb (Condition, Left, Right : W_Term_Id) return W_Term_Id
   is
   begin
      case Get_Kind (Condition) is
         when W_True_Literal =>
            return Left;

         when W_False_Literal =>
            return Right;

         when others =>
            return
               New_Operation
                  (Name       => New_Identifier ("ite"),
                   Parameters => (1 => Condition, 2 => Left, 3 => Right));
      end case;
   end New_Ifb;

   --------------
   -- New_Orb --
   --------------

   function New_Orb (Left, Right : W_Term_Id) return W_Term_Id
   is
   begin
      case Get_Kind (Left) is
         when W_False_Literal =>
            return Right;

         when others =>
            case Get_Kind (Right) is
               when W_False_Literal =>
                  return Left;

               when others =>
                  return
                     New_Operation
                        (Name       => New_Identifier ("bool_or"),
                         Parameters => (1 => Left, 2 => Right));
            end case;

      end case;
   end New_Orb;

end Why.Gen.Terms;
