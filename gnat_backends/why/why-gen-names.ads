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

with String_Utils; use String_Utils;
with Why.Ids;      use Why.Ids;
with Why.Sinfo;    use Why.Sinfo;

package Why.Gen.Names is
   --  This package provides ways to manipulate subprogram names and
   --  to create identifiers from their string representation

   function Array_Access_Name (Name : String) return W_Identifier_Id;
   --  From the name of an array type, return the name of its access function.
   --
   function Array_First_Name (Name : String) return W_Identifier_Id;
   --  From the name of an array type, return the name of its "first"
   --  function.

   function Array_First_Update (Name : String) return W_Identifier_Id;
   --  From the name of an array type, return the name of the axiom that
   --  states that "first" is constant

   function Array_Last_Name (Name : String) return W_Identifier_Id;
   --  From the name of an array type, return the name of its "last" function.

   function Array_Last_Update (Name : String) return W_Identifier_Id;
   --  From the name of an array type, return the name of the axiom that
   --  states that "last" is constant

   function Array_Length_Name (Name : String) return W_Identifier_Id;
   --  From the name of an array type, return the name of its "length"
   --  function.

   function Array_Length_Non_Zero (Name : String) return W_Identifier_Id;
   --  From the name of an array type, return the name of the axiom that
   --  defines the properties when Length is positive.

   function Array_Length_Update (Name : String) return W_Identifier_Id;
   --  From the name of an array type, return the name of the axiom that
   --  states that "length" is constant

   function Array_Length_Zero (Name : String) return W_Identifier_Id;
   --  From the name of an array type, return the name of the axiom that
   --  defines the properties when Length Zero.

   function Array_Update_Name (Name : String) return W_Identifier_Id;
   --  From the name of an array type, return the name of its update function

   function Array_Accupd_Eq_Axiom (Name : String) return W_Identifier_Id;
   --  From the name of an array type, return the name of the axiom of
   --  access/update equality

   function Array_Accupd_Neq_Axiom (Name : String) return W_Identifier_Id;
   --  From the name of an array type, return the name of the axiom of
   --  access/update with disequality

   function Coerce_Axiom (Name : String) return  W_Identifier_Id;
   function Coerce_Axiom (Name : W_Identifier_Id) return  W_Identifier_Id;
   --  From the name of an abstract type, return the name of
   --  its coerce axiom.

   function Eq_Param_Name (Name : String) return W_Identifier_Id;
   function Eq_Param_Name (Name : W_Identifier_Id) return W_Identifier_Id;
   --  From the name of an abstract type, return the name of
   --  its equality parameter.

   function Eq_Pred_Name (Name : String) return W_Identifier_Id;
   function Eq_Pred_Name (Name : W_Identifier_Id) return W_Identifier_Id;
   --  From the name of an abstract type, return the name of
   --  its equality predicate.

   function New_Bool_Int_Axiom (Rel : W_Relation) return W_Identifier_Id;
   --  Return the name of the boolean comparison axiom for Why ints that
   --  corresponds to the comparison operator in argument.

   function New_Bool_Int_Cmp (Rel : W_Relation) return W_Identifier_Id;
   --  Return the name of the boolean comparison operator for Why ints that
   --  corresponds to the comparison operator in argument.

   function New_Conversion_Axiom (From : String; To : String)
      return W_Identifier_Id;
   --  Create a new identifier for a conversion between to abstract types

   function New_Conversion_To_Int (Name : String) return W_Identifier_Id;
   --  Create a new identifier for a conversion from an abstract type
   --  to int. The name of the abstract type is given in parameter.

   function New_Conversion_From_Int (Name : String) return W_Identifier_Id;
   --  Create a new identifier for a conversion from int to an abstract type.
   --  The name of the abstract type is given in parameter.

   function New_Definition_Name (Name : String) return W_Identifier_Id;
   --  Create a new identifier for the "definition only" version of a
   --  subprogram, which is not meant to be called.

   function Logic_Func_Name (Name : String) return W_Identifier_Id;
   --  Create a new identifier for the logic version of a
   --  subprogram, which is used in annotations.

   function Logic_Func_Axiom (Name : String) return W_Identifier_Id;
   --  Create a new name for the axiom that states equivalence of
   --  a subprogram and its logic definition.

   function New_Exit_Identifier return W_Identifier_Id;
   --  Return an new identifier for the exception "Exit".

   function New_Identifier (Name : String) return W_Identifier_Id;
   --  Create a new identifier for Name and return the result

   function New_Identifiers (SL : String_Lists.List) return W_Identifier_Array;
   --  Return an array of identifiers

   function New_Ignore_Name return W_Identifier_Id;

   function New_Integer_Division return W_Identifier_Id;
   --  Return an identifier that corresponds to integer division in Why

   function New_Pre_Check_Name (Name : String) return W_Identifier_Id;
   --  Return an identifier for the subprogram that checks whether a
   --  precondition is properly guarded

   function New_Result_Identifier return W_Identifier_Id;
   --  Return an new identifier for a function result as it
   --  would be used into a postcondition.

   function New_Term (Name : String) return W_Term_Id;
   --  Return a term identified by the given name

   function New_Terms (SL : String_Lists.List) return W_Term_Array;
   --  Return an array of term identifiers

   function Range_Pred_Name (Name : String) return W_Identifier_Id;
   function Range_Pred_Name (Name : W_Identifier_Id) return W_Identifier_Id;
   --  From the name of an abstract type, return the name of
   --  its range predicate.

   function Range_Axiom (Name : String) return  W_Identifier_Id;
   function Range_Axiom (Name : W_Identifier_Id) return W_Identifier_Id;
   --  From the name of an abstract type, return the name of
   --  its range axiom.

   function Record_Getter_Name (Name : String) return W_Identifier_Id;
   function Record_Getter_Name (Name : W_Identifier_Id) return W_Identifier_Id;
   --  From the full name of a record component, return the getter for
   --  this component.

   function Record_Getter_Axiom (Name : String) return W_Identifier_Id;
   --  From the full name of a record component, return the name of
   --  its getter axiom.

   function Record_Builder_Name (Name : String) return W_Identifier_Id;
   function Record_Builder_Name
     (Name : W_Identifier_Id)
     return W_Identifier_Id;
   --  From the name of a record type, return the name of its builder.

   procedure Set_Name (Id : W_Identifier_Id; Name : String);
   --  Change the name of the given identifier

   function To_Program_Space (Name : W_Identifier_Id) return W_Identifier_Id;
   --  Create a new identifier for an entity in program space, given
   --  the name of the corresponding entity in logic space.

   function To_Term_Identifier
     (Name : W_Identifier_Id)
     return W_Term_Id;
   --  Create a label identifier from Name. Name is duplicated.

   function Unicity_Axiom (Name : String) return  W_Identifier_Id;
   function Unicity_Axiom (Name : W_Identifier_Id) return  W_Identifier_Id;
   --  From the name of an abstract type, return the name of
   --  its unicity axiom.

end Why.Gen.Names;
