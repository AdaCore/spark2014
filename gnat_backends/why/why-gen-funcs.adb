------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                        W H Y - G E N - F U N C S                         --
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

with Why.Atree.Builders;  use Why.Atree.Builders;

with Why.Gen.Decl;        use Why.Gen.Decl;
with Why.Gen.Names;       use Why.Gen.Names;
with Why.Gen.Preds;       use Why.Gen.Preds;
with Why.Gen.Terms;       use Why.Gen.Terms;

package body Why.Gen.Funcs is

   ------------------------------------
   -- New_Boolean_Equality_Parameter --
   ------------------------------------

   procedure New_Boolean_Equality_Parameter
      (File          : W_File_Id;
       Type_Name     : String)
   is
      Arg_S : constant String := "n";
      Arg_T : constant String := "m";
      Post  : constant W_Predicate_Id :=
         New_Conditional_Pred
           (Condition => New_Result_Term,
            Then_Part =>
              New_Equal (New_Term (Arg_S), New_Term (Arg_T)),
            Else_Part =>
              New_NEqual (New_Term (Arg_S), New_Term (Arg_T)));
   begin
      New_Parameter
        (File => File,
         Name => Eq_Param_Name.Id (Type_Name),
         Binders =>
            (1 =>
               New_Binder
                  (Names => (1 => New_Identifier (Arg_S),
                             2 => New_Identifier (Arg_T)),
                   Arg_Type =>
                     New_Abstract_Type (Name => New_Identifier (Type_Name)))),
         Return_Type => New_Type_Bool,
         Post        => Post);
   end New_Boolean_Equality_Parameter;

end Why.Gen.Funcs;
