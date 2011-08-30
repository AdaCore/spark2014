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

with Types;        use Types;
with Why.Ids;      use Why.Ids;
with Why.Sinfo;    use Why.Sinfo;
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
      Component : String;
      First     : Uint;
      Last      : Uint);
   --  Introduce all the necessary declarations for an Ada array declaration
   --  of the form
   --  type A is Array (index) of Component

   procedure Declare_Ada_Unconstrained_Array
     (File      : W_File_Id;
      Name      : String;
      Component : String);
   --  Introduce all the necessary declarations for an Ada array declaration
   --  of the form
   --  type A is Array (basetype range <>) of Component

   function New_Array_Access
     (Ada_Node      : Node_Id;
      Type_Name     : String;
      Ar            : W_Expr_Id;
      Index         : W_Expr_Id;
      Domain        : EW_Domain) return W_Expr_Id;
   --  Generate an expr that corresponds to an array access.

   function New_Array_First
      (Type_Name : String;
       Ar        : W_Expr_Id;
       Domain    : EW_Domain) return W_Expr_Id;
   --  Generate an expr that corresponds to Ar'First.

   function New_Array_Last
      (Type_Name : String;
       Ar        : W_Expr_Id;
       Domain    : EW_Domain) return W_Expr_Id;
   --  Generate an expr that corresponds to Ar'Last.

   function New_Array_Length
      (Type_Name : String;
       Ar        : W_Expr_Id;
       Domain    : EW_Domain) return W_Expr_Id;
   --  Generate an expr that corresponds to Ar'Length.

   function New_Array_Update_Prog
      (Ada_Node  : Node_Id;
       Type_Name : String;
       Ar        : W_Identifier_Id;
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
