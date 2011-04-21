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

with Why.Conversions;     use Why.Conversions;
with Why.Atree.Builders;  use Why.Atree.Builders;

with Why.Gen.Decl;        use Why.Gen.Decl;
with Why.Gen.Names;       use Why.Gen.Names;
with Why.Gen.Preds;       use Why.Gen.Preds;
with Why.Gen.Terms;       use Why.Gen.Terms;

package body Why.Gen.Funcs is

   ----------------------------------
   -- Declare_Logic_And_Parameters --
   ----------------------------------

   procedure Declare_Logic_And_Parameters
     (File        : W_File_Id;
      Name        : W_Identifier_Id;
      Binders     : W_Binder_Array;
      Return_Type : W_Primitive_Type_Id;
      Pre         : W_Predicate_OId := Why_Empty;
      Post        : W_Predicate_OId := Why_Empty)
   is
      Program_Space_Name : constant W_Identifier_Id :=
                             To_Program_Space (Name);
      Final_Post         : W_Predicate_OId := Post;
   begin
      New_Logic
        (File        => File,
         Name        => Name,
         Binders     => Binders,
         Return_Type => W_Logic_Return_Type_Id (Return_Type));

      if Final_Post = Why_Empty then
         declare
            Logic_Name : constant W_Identifier_Id :=
                           +Duplicate_Any_Node (Id => +Name);
         begin
            Final_Post := New_Related_Terms
              (Left  => New_Call_To_Logic (Logic_Name, Binders),
               Op    => New_Rel_Eq,
               Right => New_Result_Term);
         end;
      end if;

      New_Parameter
         (File        => File,
          Name        => Program_Space_Name,
          Binders     => Binders,
          Return_Type => +Duplicate_Any_Node (Id => +Return_Type),
          Pre         => New_Assertion (Pred => Pre),
          Post        => New_Assertion (Pred => Final_Post),
          Effects     => New_Effects);
   end Declare_Logic_And_Parameters;

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
         Name => Eq_Param_Name (Type_Name),
         Binders =>
            (1 =>
               New_Binder
                  (Names => (1 => +New_Identifier (Arg_S),
                             2 => +New_Identifier (Arg_T)),
                   Arg_Type =>
                     New_Abstract_Type (Name => +New_Identifier (Type_Name)))),
         Return_Type => New_Type_Bool,
         Post        => New_Assertion (Pred => Post));
   end New_Boolean_Equality_Parameter;

end Why.Gen.Funcs;
