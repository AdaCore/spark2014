------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                        W H Y - G E N - N A M E S                         --
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

with Why.Ids;   use Why.Ids;
with Why.Sinfo; use Why.Sinfo;

package Why.Gen.Names is
   --  This package provides ways to manipulate subprogram names and
   --  to create identifiers from their string representation

   function New_Definition_Name (Name : String) return String;
   --  Create a new identifier for the "definition only" version of a
   --  subprogram, which is not meant to be called.

   function New_Identifier (Name : String) return W_Identifier_Id;
   --  Create a new identifier for Name and return the result

   function New_Conversion_Axiom (From : String; To : String)
      return W_Identifier_Id;
   --  Create a new identifier for a conversion between to abstract types

   function New_Conversion_To_Int (Name : String) return W_Identifier_Id;
   --  Create a new identifier for a conversion from an abstract type
   --  to int. The name of the abstract type is given in parameter.

   function New_Conversion_From_Int (Name : String) return W_Identifier_Id;
   --  Create a new identifier for a conversion from int to an abstract type.
   --  The name of the abstract type is given in parameter.

   function Range_Pred_Name (Name : String) return W_Identifier_Id;
   function Range_Pred_Name (Name : W_Identifier_Id) return W_Identifier_Id;
   --  From the name of an abstract type, return the name of
   --  its range predicate.

   function Eq_Param_Name (Name : String) return W_Identifier_Id;
   function Eq_Param_Name (Name : W_Identifier_Id) return W_Identifier_Id;
   --  From the name of an abstract type, return the name of
   --  its equality parameter.

   function Eq_Pred_Name (Name : String) return W_Identifier_Id;
   function Eq_Pred_Name (Name : W_Identifier_Id) return W_Identifier_Id;
   --  From the name of an abstract type, return the name of
   --  its equality predicate.

   function Range_Axiom (Name : String) return  W_Identifier_Id;
   function Range_Axiom (Name : W_Identifier_Id) return W_Identifier_Id;
   --  From the name of an abstract type, return the name of
   --  its range axiom.

   function Coerce_Axiom (Name : String) return  W_Identifier_Id;
   function Coerce_Axiom (Name : W_Identifier_Id) return  W_Identifier_Id;
   --  From the name of an abstract type, return the name of
   --  its coerce axiom.

   function Unicity_Axiom (Name : String) return  W_Identifier_Id;
   function Unicity_Axiom (Name : W_Identifier_Id) return  W_Identifier_Id;
   --  From the name of an abstract type, return the name of
   --  its unicity axiom.

   function Allocator_Name (Name : String) return W_Identifier_Id;
   --  From the name of an abstract type, return the name of
   --  its allocator.

   function To_Program_Space (Name : W_Identifier_Id) return W_Identifier_Id;
   --  Create a new identifier for an entity in program space, given
   --  the name of the corresponding entity in logic space.

   function Safe_Version (Name : W_Identifier_Id) return W_Identifier_Id;
   --  Create a new identifier for the "safe" version (no precondition
   --  for run-time checks) of a program-space subprogram (a so-called
   --  "parameter").

   procedure Set_Name (Id : W_Identifier_Id; Name : String);
   --  Change the name of the given identifier

   function New_Result_Identifier return W_Term_Identifier_Id;
   --  Return an new identifier for a function result as it
   --  would be used into a postcondition.

   function New_Exit_Identifier return W_Identifier_Id;
   --  Return an new identifier for the exception "Exit".

   function To_Term_Identifier
     (Name : W_Identifier_Id)
     return W_Term_Identifier_Id;
   --  Create a label identifier from Name. Name is duplicated.

   function New_Term (Name : String) return W_Term_Identifier_Id;
   --  Return a term identified by the given name

   function Array_Access_Name (Name : String) return W_Identifier_Id;
   --  From the name of an array type, return the name of its access function
   --
   function Array_Update_Name (Name : String) return W_Identifier_Id;
   --  From the name of an array type, return the name of its update function

   function Array_Accupd_Eq_Axiom (Name : String) return W_Identifier_Id;
   --  From the name of an array type, return the name of the axiom of
   --  access/update equality

   function New_Bool_Int_Axiom (Rel : W_Relation) return W_Identifier_Id;
   --  Return the name of the boolean comparison axiom for Why ints that
   --  corresponds to the comparison operator in argument.

   function New_Bool_Int_Cmp (Rel : W_Relation) return W_Identifier_Id;
   --  Return the name of the boolean comparison operator for Why ints that
   --  corresponds to the comparison operator in argument.
end Why.Gen.Names;
