------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                        W H Y - G E N - F U N C S                         --
--                                                                          --
--                                 S p e c                                  --
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

with Why.Ids;              use Why.Ids;
with Why.Types;            use Why.Types;

package Why.Gen.Funcs is
   --  This package provides facilities to generate subprograms declarations
   --  in the program space and in the logic space.

   function New_Call_To_Logic
     (Name    : W_Identifier_Id;
      Binders : W_Binder_Array)
     return W_Term_Id;
   --  Create a call to an operation in the logical space with parameters
   --  taken from Binders. Typically, from:
   --
   --     (x1 : type1) (x2 : type2)
   --
   --  ...it produces:
   --
   --     operation_name (x1, x2)

   procedure Declare_Logic_And_Parameters
     (File        : W_File_Id;
      Name        : W_Identifier_Id;
      Binders     : W_Binder_Array;
      Return_Type : W_Primitive_Type_Id;
      Pre         : W_Predicate_OId := Why_Empty;
      Post        : W_Predicate_OId := Why_Empty);
   --  Create a logic declaration and it corresponding declaration in
   --  the program space (safe and default) and append it to File. Name
   --  is the name of the logic function declaration, Binders is the
   --  spec of the default program declaration; all params will be merged
   --  as is into the resulting syntax tree.
   --
   --  If no postcondition is given, one will be generated that will use the
   --  logic function. e.g. if Name is "my_func" and Binders is:
   --
   --     (x1 : type1) -> (x2 : type2)
   --
   --  ...then the logic declaration will be:
   --
   --     logic my_func : type1, type2 -> type3
   --
   --  ...and the generated program-space declaration, with the default
   --  postcondition will be:
   --
   --     parameter my_func_ :
   --      x1 : type1 -> x2 : type2 ->
   --     { some_precondition }
   --      type3
   --     { my_func (x1, x2) = result }

   procedure New_Boolean_Equality_Parameter
      (File          : W_File_Id;
       Type_Name     : String);
      --  Create a parameter of the form
      --     parameter <eq_param_name> : (m : type) -> (n : type) ->
      --        {} bool { if result then m = n else m <> n }

end Why.Gen.Funcs;
