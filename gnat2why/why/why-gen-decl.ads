------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                        W H Y - G E N - D E C L                           --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                       Copyright (C) 2010-2013, AdaCore                   --
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

with Why.Ids; use Why.Ids;

package Why.Gen.Decl is
   --  This package contains all subprograms that are used to build Why
   --  toplevel declarations.

   function New_Type (Name : String) return W_Declaration_Id;

   function New_Type
     (Name  : W_Identifier_Id;
      Alias : W_Primitive_Type_Id) return W_Declaration_Id;

   function New_Type
     (Name : W_Identifier_Id;
      Args : Natural)
     return W_Declaration_Id;
   --  Declare a new abstract type. If Args is given, declare a polymorphic
   --  abstract type with the given number of arguments.

   function New_Adt_Definition
     (Name         : W_Identifier_Id;
      Constructors : W_Constr_Decl_Array)
     return W_Declaration_Id;

   procedure Emit
     (Theory : W_Theory_Declaration_Id;
      Decl : W_Declaration_Id);

end Why.Gen.Decl;
