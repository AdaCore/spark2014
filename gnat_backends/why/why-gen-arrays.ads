------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                        W H Y - G E N - A R R A Y S                       --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                       Copyright (C) 2010-2012, AdaCore                   --
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

with Snames;    use Snames;
with Types;     use Types;
with Uintp;     use Uintp;
with Why.Ids;   use Why.Ids;
with Why.Sinfo; use Why.Sinfo;

package Why.Gen.Arrays is
   --  This package encapsulates the encoding of Ada arrays into Why.

   --  For an Ada array type declaration with range constraints, we introduce
   --  an abstract type in Why, with access/update functions. This allows
   --  getting for free the range properties of arrays in Why.

   --  We are limited to constrained arrays with static bounds for now.

   procedure Declare_Ada_Array
     (File   : W_File_Id;
      Name   : String;
      Entity : Entity_Id);
   --  Introduce all the necessary declarations for an Ada array declaration
   --  of the form
   --  type A is Array (index) of Component

   procedure Declare_Ada_Unconstrained_Array
     (File   : W_File_Id;
      Name   : String;
      Entity : Entity_Id);
   --  Introduce all the necessary declarations for an Ada array declaration
   --  of the form
   --  type A is Array (basetype range <>) of Component

   function New_Array_Access
     (Ada_Node  : Node_Id;
      Type_Name : String;
      Ar        : W_Expr_Id;
      Index     : W_Expr_Array;
      Domain    : EW_Domain;
      Dimension : Pos) return W_Expr_Id;
   --  Generate an expr that corresponds to an array access.

   function New_Array_Attr
      (Attr      : Attribute_Id;
       Type_Name : String;
       Ar        : W_Expr_Id;
       Domain    : EW_Domain;
       Dimension : Pos;
       Argument  : Uint) return W_Expr_Id
       with Pre =>
         (Attr in Attribute_First | Attribute_Last | Attribute_Length);
   --  Generate an expr that corresponds to Ar'Attr

   function New_Array_Update
      (Ada_Node  : Node_Id;
       Type_Name : String;
       Ar        : W_Expr_Id;
       Index     : W_Expr_Array;
       Value     : W_Expr_Id;
       Domain    : EW_Domain;
       Dimension : Pos) return W_Expr_Id;

end Why.Gen.Arrays;
