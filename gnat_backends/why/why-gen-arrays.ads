------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                        W H Y - G E N - A R R A Y S                       --
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

with Types;        use Types;
with Why.Ids;      use Why.Ids;
with Uintp;        use Uintp;

package Why.Gen.Arrays is
   --  This package encapsulates the encoding of Ada arrays into Why.

   --  For an Ada array type declaration with range constraints, we introduce
   --  an abstract type in Why, with access/update functions. This allows
   --  getting for free the range properties of arrays in Why.

   --  We are limited to constrained arrays with static bounds for now.

   procedure Declare_Ada_Constrained_Array
     (File      : W_File_Id;
      Name      : String;
      Index     : String;
      Component : String;
      First     : Uint;
      Last      : Uint);
   --  Introduce all the necessary declarations for an Ada array declaration
   --  of the form
   --  type A is Array (index) of Component

   procedure Declare_Ada_Unconstrained_Array
     (File      : W_File_Id;
      Name      : String;
      Index     : String;
      Component : String);
   --  Introduce all the necessary declarations for an Ada array declaration
   --  of the form
   --  type A is Array (basetype range <>) of Component

   procedure Declare_Generic_Array_Type (File : W_File_Id);
   --  Introduce the generic Array Type that represents Ada arrays

   function New_Array_Access_Prog
     (Ada_Node      : Node_Id;
      Type_Name     : String;
      Ar            : W_Prog_Id;
      Index         : W_Prog_Id;
      Unconstrained : Boolean) return W_Prog_Id;
   --  Generate a Program that corresponds to an array access.

   function New_Array_Access_Term
      (Type_Name : String;
       Ar        : W_Term_Id;
       Index     : W_Term_Id) return W_Term_Id;
   --  Generate a Term that corresponds to an array access.

   function New_Array_First_Term
      (Type_Name : String;
       Ar        : W_Term_Id) return W_Term_Id;
   --  Generate a Term that corresponds to Ar'First.

   function New_Array_Last_Term
      (Type_Name : String;
       Ar        : W_Term_Id) return W_Term_Id;
   --  Generate a Term that corresponds to Ar'Last.

   function New_Array_Length_Term
      (Type_Name : String;
       Ar        : W_Term_Id) return W_Term_Id;
   --  Generate a Term that corresponds to Ar'Length.

   function New_Array_Update_Prog
      (Ada_Node      : Node_Id;
       Type_Name     : String;
       Ar            : W_Identifier_Id;
       Index         : W_Prog_Id;
       Value         : W_Prog_Id;
       Unconstrained : Boolean) return W_Prog_Id;
   --  Generate an assignment that corresponds to an array update in Why
   --  programs.

   function New_Array_Update_Term
      (Type_Name : String;
       Ar        : W_Term_Id;
       Index     : W_Term_Id;
       Value     : W_Term_Id) return W_Term_Id;
   --  Generate a Program that corresponds to an array update.

   function New_Array_First_Prog
      (Type_Name : String;
       Ar        : W_Prog_Id) return W_Prog_Id;
   --  Generate a Prog that corresponds to Ar'First.

   function New_Array_Last_Prog
      (Type_Name : String;
       Ar        : W_Prog_Id) return W_Prog_Id;
   --  Generate a Prog that corresponds to Ar'Last.

   function New_Array_Length_Prog
      (Type_Name : String;
       Ar        : W_Prog_Id) return W_Prog_Id;
   --  Generate a Prog that corresponds to Ar'Length.

end Why.Gen.Arrays;
