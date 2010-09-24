------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                        W H Y - G E N - N A M E S                         --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                       Copyright (C) 2010, AdaCore                        --
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

with Why.Ids; use Why.Ids;

package Why.Gen.Names is
   --  This package provides ways to manipulate subprogram names and
   --  to create identifiers from their string representation

   function New_Identifier (Name : String) return W_Identifier_Id;
   --  Create a new identifier for Name and return the result

   function New_Conversion_To_Int (Name : String) return W_Identifier_Id;
   --  Create a new identifier for a conversion from an abstract type
   --  to int. The name of the astract type is given in parameter.

   function To_Program_Space (Name : W_Identifier_Id) return W_Identifier_Id;
   --  Create a new identifier for an entity in program space, given
   --  the name of the corresponding entity in logic space.

   function Safe_Version (Name : W_Identifier_Id) return W_Identifier_Id;
   --  Create a new identifier for the "safe" version (no precondition
   --  for run-time checks) of a program-space subprogram (a so-called
   --  "parameter").

   procedure Set_Name (Id : W_Identifier_Id; Name : String);
   --  Change the name of the given identifier

   function New_Result_Identifier return W_Label_Identifier_Id;
   --  Return an new identifier for a function result as it
   --  would be used into a postcondition.

   function To_Label_Identifier
     (Name : W_Identifier_Id)
     return W_Label_Identifier_Id;
   --  Create a label identifier from Name. Name is duplicated.

end Why.Gen.Names;
