------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                        W H Y - G E N - D E C L                           --
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

with Types;   use Types;
with Why.Atree.Builders; use Why.Atree.Builders;
with Why.Ids; use Why.Ids;

package Why.Gen.Decl is
   --  This package contains all subprograms that are used to build Why
   --  toplevel declarations.
   --
   --  Overloaded procedures with a W_File_Id Argument add the built
   --  declaration to that context instead of returning it

   procedure New_Abstract_Type (File : W_File_Id; Name : String);
   procedure New_Abstract_Type (File : W_File_Id; Name : W_Identifier_Id);

   procedure New_Adt_Definition
     (File : W_Type_Id;
      Name : W_Identifier_Id;
      Constructors : W_Constr_Decl_Array);

   procedure New_Axiom
      (File       : W_File_Id;
       Name       : W_Identifier_Id;
       Axiom_Body : W_Predicate_Id);
   --  Declare an axiom with the given name and the given body.

   procedure New_Global_Binding
      (File    : W_File_Id;
       Name    : String;
       Binders : W_Binder_Array;
       Pre     : W_Assertion_Id
                   := New_Assertion (Pred => New_True_Literal_Pred);
       Def     : W_Prog_Id;
       Post    : W_Assertion_Id
                   := New_Assertion (Pred => New_True_Literal_Pred));

   procedure New_Include_Declaration
     (File : W_File_Id;
      Name : W_Identifier_Id;
      Ada_Node : Node_Id := Empty);
   --  Include declarations, of the form
   --    include "name.why"

   procedure New_Logic
     (File        : W_File_Id;
      Name        : W_Identifier_Id;
      Args        : W_Logic_Arg_Type_Array;
      Return_Type : W_Logic_Return_Type_Id);

   procedure New_Predicate_Definition
     (File     : W_File_Id;
      Name     : W_Identifier_Id;
      Binders  : W_Logic_Binder_Array;
      Def      : W_Predicate_Id);

end Why.Gen.Decl;
