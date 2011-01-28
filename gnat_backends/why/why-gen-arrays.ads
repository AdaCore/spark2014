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

with Uintp;        use Uintp;
with Why.Ids;      use Why.Ids;

package Why.Gen.Arrays is
   --  This package encapsulates the encoding of Ada arrays into Why.

   --  For an Ada array type declaration with range constraints, we introduce
   --  an abstract type in Why, with access/update functions. This allows
   --  getting for free the range properties of arrays in Why.

   --  We are limited to constrained arrays with static bounds for now.

   procedure Declare_Ada_Constrained_Array
     (File      : W_File_Id;
      Name      : String;
      Int_Name  : String;
      Component : String;
      Low       : Uint;
      High      : Uint);
   --  Introduce all the necessary declarations for an Ada array declaration
   --  of the form
   --  type A is Array (low..high) of Component

   function New_Array_Access_Prog
      (Type_Name : String;
       Ar        : W_Prog_Id;
       Index     : W_Prog_Id) return W_Prog_Id;
   --  Generate a Program that corresponds to an array access.

   function New_Array_Access_Term
      (Type_Name : String;
       Ar        : W_Term_Id;
       Index     : W_Term_Id) return W_Term_Id;
   --  Generate a Term that corresponds to an array access.

   function New_Array_Update_Prog
      (Type_Name : String;
       Ar        : W_Prog_Id;
       Index     : W_Prog_Id;
       Value     : W_Prog_Id) return W_Prog_Id;
   --  Generate an assignment that corresponds to an array update in Why
   --  programs.

   function New_Array_Update_Term
      (Type_Name : String;
       Ar        : W_Term_Id;
       Index     : W_Term_Id;
       Value     : W_Term_Id) return W_Term_Id;
   --  Generate a Program that corresponds to an array update.
end Why.Gen.Arrays;
