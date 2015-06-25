------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                        W H Y - G E N - D E C L                           --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                       Copyright (C) 2010-2015, AdaCore                   --
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

   function New_Type_Decl (Name : String) return W_Declaration_Id;

   function New_Type_Decl
     (Name  : W_Name_Id;
      Alias : W_Type_Id) return W_Declaration_Id;

   function New_Havoc_Declaration (Name : W_Name_Id) return W_Declaration_Id;
   --  @param  Name name of the type for which we want a havoc function
   --  @return Definition of a val havocing its only argument of type name__ref

   function New_Ref_Type_Definition (Name : W_Name_Id) return W_Declaration_Id;
   --  @param  Name name of the type for which we want a reference
   --  @return Definition of a record type with one mutable field of type Name

   procedure Emit
     (Theory : W_Theory_Declaration_Id;
      Decl : W_Declaration_Id);

end Why.Gen.Decl;
