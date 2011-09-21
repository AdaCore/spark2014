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

with Why.Conversions;    use Why.Conversions;
with Why.Sinfo;          use Why.Sinfo;
with Why.Atree.Builders; use Why.Atree.Builders;
with Why.Gen.Decl;       use Why.Gen.Decl;
with Why.Gen.Names;      use Why.Gen.Names;
with Why.Gen.Terms;      use Why.Gen.Terms;
with Why.Gen.Binders;    use Why.Gen.Binders;

package body Why.Gen.Funcs is

   ------------------------------------
   -- New_Boolean_Equality_Parameter --
   ------------------------------------

   procedure New_Boolean_Equality_Parameter
      (File          : W_File_Id;
       Type_Name     : String)
   is
      Arg_S    : constant String := "n";
      Arg_T    : constant String := "m";
      True_Term : constant W_Term_Id :=
                  New_Literal (Value => EW_True);
      Cond     : constant W_Pred_Id :=
                  New_Relation
                     (Left    => +New_Result_Term,
                      Op_Type => EW_Bool,
                      Right   => +True_Term,
                      Op      => EW_Eq);
      Then_Rel : constant W_Pred_Id :=
                 New_Relation
                   (Op      => EW_Eq,
                    Op_Type => EW_Bool,
                    Left    => +New_Term (Arg_S),
                    Right   => +New_Term (Arg_T));
      Else_Rel : constant W_Pred_Id :=
                 New_Relation
                   (Op      => EW_Ne,
                    Op_Type => EW_Bool,
                    Left    => +New_Term (Arg_S),
                    Right   => +New_Term (Arg_T));
      Post    : constant W_Pred_Id :=
                  New_Conditional
                    (Condition => +Cond,
                     Then_Part => +Then_Rel,
                     Else_Part => +Else_Rel);
      Pre     : constant W_Pred_Id :=
                  New_Literal (Value => EW_True);
      Arg_Type : constant W_Primitive_Type_Id :=
                   New_Abstract_Type (Name => New_Identifier (EW_Term,
                                                              Type_Name));
   begin
      Emit
        (File,
         New_Function_Decl
           (Domain      => EW_Prog,
            Name        => Eq_Param_Name.Id (Type_Name),
            Binders     =>
              (1 =>
                 (B_Name => New_Identifier (Arg_S),
                  B_Type => Arg_Type,
                  others => <>),
               2 =>
                 (B_Name => New_Identifier (Arg_T),
                  B_Type => Arg_Type,
                  others => <>)),
            Return_Type => New_Base_Type (Base_Type => EW_Bool),
            Pre         => Pre,
            Post        => Post));
   end New_Boolean_Equality_Parameter;

end Why.Gen.Funcs;
