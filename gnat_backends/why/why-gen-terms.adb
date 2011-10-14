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
-- gnat2why is  free  software;  you can redistribute  it and/or  modify it --
-- under terms of the  GNU General Public License as published  by the Free --
-- Software  Foundation;  either version 3,  or (at your option)  any later --
-- version.  gnat2why is distributed  in the hope that  it will be  useful, --
-- but WITHOUT ANY WARRANTY; without even the implied warranty of  MERCHAN- --
-- TABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public --
-- License for  more details.  You should have  received  a copy of the GNU --
-- General  Public License  distributed with  gnat2why;  see file COPYING3. --
-- If not,  go to  http://www.gnu.org/licenses  for a complete  copy of the --
-- license.                                                                 --
--                                                                          --
-- gnat2why is maintained by AdaCore (http://www.adacore.com)               --
--                                                                          --
------------------------------------------------------------------------------

with Why.Sinfo;           use Why.Sinfo;
with Why.Atree.Accessors; use Why.Atree.Accessors;
with Why.Atree.Builders;  use Why.Atree.Builders;
with Why.Atree.Tables;    use Why.Atree.Tables;
with Why.Conversions;     use Why.Conversions;
with Why.Gen.Names;       use Why.Gen.Names;

package body Why.Gen.Terms is

   -------------
   -- New_Ifb --
   -------------

   function New_Ifb (Condition, Left, Right : W_Term_Id) return W_Term_Id
   is
   begin
      case Get_Kind (+Condition) is
         when W_Literal =>
            if Get_Value (+Condition) = EW_True then
               return Left;
            else
               return Right;
            end if;

         when others =>
            return
              New_Call
                (Name => New_Identifier ("ite"),
                 Args => (1 => +Condition, 2 => +Left, 3 => +Right));
      end case;
   end New_Ifb;

   ---------------------
   -- New_Result_Term --
   ---------------------

   function New_Result_Term return W_Term_Id
   is
   begin
      return +New_Result_Identifier.Id;
   end New_Result_Term;

   ----------------------------
   -- New_Simpl_Epsilon_Term --
   ----------------------------

   function New_Simpl_Epsilon_Term
     (T : W_Primitive_Type_Id) return W_Term_Id is
   begin
      return
        New_Epsilon
          (Binder =>
               New_Binder (Domain   => EW_Term,
                           Name     => New_Identifier ("x"),
                           Arg_Type => +T),
           Pred   => New_Literal (Value => EW_True));
   end New_Simpl_Epsilon_Term;

   function New_Simpl_Epsilon_Term
     (T    : W_Primitive_Type_Id;
      Id   : W_Identifier_Id;
      Pred : W_Pred_Id) return W_Term_Id is
   begin
      return
        New_Epsilon
          (Binder =>
               New_Binder (Domain   => EW_Term,
                           Name     => Id,
                           Arg_Type => +T),
           Pred   => Pred);
   end New_Simpl_Epsilon_Term;

end Why.Gen.Terms;
