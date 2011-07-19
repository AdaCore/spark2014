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

with String_Utils; use String_Utils;
with Why.Ids;      use Why.Ids;
with Why.Sinfo;    use Why.Sinfo;

with Why.Gen.Name_Gen;

package Why.Gen.Names is
   --  This package provides ways to manipulate subprogram names and
   --  to create identifiers from their string representation

   function New_Bool_Int_Axiom (Rel : W_Relation) return W_Identifier_Id;
   --  Return the name of the boolean comparison axiom for Why ints that
   --  corresponds to the comparison operator in argument.

   function New_Bool_Int_Cmp (Rel : W_Relation) return W_Identifier_Id;
   --  Return the name of the boolean comparison operator for Why ints that
   --  corresponds to the comparison operator in argument.

   function New_Conversion_Axiom (From : String; To : String)
      return W_Identifier_Id;
   --  Create a new identifier for a conversion between to abstract types

   function New_Exit_Identifier return W_Identifier_Id;
   --  Return an new identifier for the exception "Exit".

   function New_Identifier (Name : String) return W_Identifier_Id;
   --  Create a new identifier for Name and return the result

   function New_Identifiers (SL : String_Lists.List) return W_Identifier_Array;
   --  Return an array of identifiers

   function New_Ignore_Name return W_Identifier_Id;

   function New_Integer_Division return W_Identifier_Id;
   --  Return an identifier that corresponds to integer division in Why

   function New_Result_Exc_Identifier return W_Identifier_Id;
   --  Return a new identifier for the exception used for returning from a
   --  subprogram.

   function New_Result_Identifier return W_Identifier_Id;
   --  Return a new identifier for a function result as it
   --  would be used into a postcondition.

   function New_Result_Temp_Identifier return W_Identifier_Id;
   --  Return a new identifier for the temporary used to store a function's
   --  result.

   function New_Term (Name : String) return W_Term_Id;
   --  Return a term identified by the given name

   function New_Terms (SL : String_Lists.List) return W_Term_Array;
   --  Return an array of term identifiers

   function To_Program_Space (Name : W_Identifier_Id) return W_Identifier_Id;
   --  Create a new identifier for an entity in program space, given
   --  the name of the corresponding entity in logic space.

   function To_Term_Identifier
     (Name : W_Identifier_Id)
     return W_Term_Id;
   --  Create a label identifier from Name. Name is duplicated.

   Ada_Array                : constant String := "t__ada_array";
   Array_Access             : constant String := "access";
   Array_First              : constant String := "first";
   Array_First_Upd          : constant String := "first_update";
   Array_Last               : constant String := "last";
   Array_Last_Upd           : constant String := "last_update";
   Array_Length             : constant String := "length";
   Array_Len_Nzero          : constant String := "length_non_zero";
   Array_Len_Upd            : constant String := "length_update";
   Array_Len_Zero           : constant String := "length_zero";
   Array_Update             : constant String := "update";
   Array_Accupd_Eq          : constant String := "accupd_eq";
   Array_Accupd_Neq         : constant String := "accupd_neq";
   Array_Convert_From       : constant String := "to_ada_array";
   Array_Convert_To         : constant String := "of_ada_array";
   Array_First_Static_Name  : constant String := "static_first";
   Array_Last_Static_Name   : constant String := "static_last";
   Array_Length_Static_Name : constant String := "static_length";
   Array_Conv_Idemp         : constant String := "conv_idem";
   Array_Conv_Idemp_2       : constant String := "conv_idem_2";
   Coerce                   : constant String := "coerce";
   Boolean_Eq               : constant String := "eq_bool";
   Eq_Pred                  : constant String := "eq";
   Record_Get               : constant String := "get";
   Record_Get_Axiom         : constant String := "getter";
   Record_Make              : constant String := "make";
   Of_Int                   : constant String := "of_int";
   Int_Of                   : constant String := "to_int";
   Definition               : constant String := "def";
   Logic_Def_Axiom          : constant String := "logic_def_axiom";
   Pre_Check                : constant String := "pre_check";
   Range_Name               : constant String := "range";
   In_Range                 : constant String := "in_range";
   Unicity                  : constant String := "unicity";

   package Array_Access_Name is new Name_Gen ("", Array_Access);
   --  From the name of an array type, return the name of its access function.

   package Array_Accupd_Eq_Axiom is new Name_Gen ("", Array_Accupd_Eq);
   --  From the name of an array type, return the name of the axiom of
   --  access/update equality

   package Array_Accupd_Neq_Axiom is new Name_Gen ("", Array_Accupd_Neq);
   --  From the name of an array type, return the name of the axiom of
   --  access/update with disequality

   package Array_Conv_To is new Name_Gen ("", Array_Convert_To);
   --  From the name of an array type, return the name of the conversion from
   --  Ada__Array.

   package Array_Conv_From is new Name_Gen ("", Array_Convert_From);
   --  From the name of an array type, return the name of the conversion to
   --  Ada__Array.

   package Array_Conv_Idem is new Name_Gen ("", Array_Conv_Idemp);

   package Array_Conv_Idem_2 is new Name_Gen ("", Array_Conv_Idemp_2);

   package Array_First_Name is new Name_Gen ("", Array_First);
   --  From the name of an array type, return the name of its "first"
   --  function.

   package Array_First_Update is new Name_Gen ("", Array_First_Upd);
   --  From the name of an array type, return the name of the axiom that
   --  states that "first" is constant

   package Array_Last_Name is new Name_Gen ("", Array_Last);
   --  From the name of an array type, return the name of its "last" function.

   package Array_Last_Update is new Name_Gen ("", Array_Last_Upd);
   --  From the name of an array type, return the name of the axiom that
   --  states that "last" is constant

   package Array_Length_Name is new Name_Gen ("", Array_Length);
   --  From the name of an array type, return the name of its "length"
   --  function.

   package Array_Length_Non_Zero is new Name_Gen ("", Array_Len_Nzero);
   --  From the name of an array type, return the name of the axiom that
   --  defines the properties when Length is positive.

   package Array_Length_Update is new Name_Gen ("", Array_Len_Upd);
   --  From the name of an array type, return the name of the axiom that
   --  states that "length" is constant

   package Array_Length_Zero is new Name_Gen ("", Array_Len_Zero);
   --  From the name of an array type, return the name of the axiom that
   --  defines the properties when Length Zero.

   package Array_Update_Name is new Name_Gen ("", Array_Update);
   --  From the name of an array type, return the name of its update function

   package Array_First_Static is new Name_Gen ("", Array_First_Static_Name);
   --  From the name of an array type, return the name of the axiom that
   --  states that 'First is static.

   package Array_Last_Static is new Name_Gen ("", Array_Last_Static_Name);
   --  From the name of an array type, return the name of the axiom that
   --  states that 'Last is static.

   package Array_Length_Static is new Name_Gen ("", Array_Length_Static_Name);
   --  From the name of an array type, return the name of the axiom that
   --  states that 'Length is static.

   package Coerce_Axiom is new Name_Gen ("", Coerce);
   --  From the name of an abstract type, return the name of
   --  its coerce axiom.

   package Eq_Param_Name is new Name_Gen ("", "___" & Boolean_Eq & "_", "");
   --  From the name of an abstract type, return the name of
   --  its equality parameter.

   package Eq_Pred_Name is new Name_Gen ("", Eq_Pred);
   --  From the name of an abstract type, return the name of
   --  its equality predicate.

   package New_Conversion_To_Int is new Name_Gen ("", Int_Of);
   --  Create a new identifier for a conversion from an abstract type
   --  to int. The name of the abstract type is given in parameter.

   package New_Conversion_From_Int is new Name_Gen ("", Of_Int);
   --  Create a new identifier for a conversion from int to an abstract type.
   --  The name of the abstract type is given in parameter.

   package New_Definition_Name is new Name_Gen ("", Definition);
   --  Create a new identifier for the "definition only" version of a
   --  subprogram, which is not meant to be called.

   package Logic_Func_Name is new Name_Gen ("", "", "");
   --  Create a new identifier for the logic version of a
   --  subprogram, which is used in annotations.

   package Logic_Func_Axiom is new Name_Gen ("", Logic_Def_Axiom);
   --  Create a new name for the axiom that states equivalence of
   --  a subprogram and its logic definition.

   package New_Pre_Check_Name is new Name_Gen (Pre_Check, "");
   --  Return an identifier for the subprogram that checks whether a
   --  precondition is properly guarded

   package Program_Func_Name is new Name_Gen ("", "_", "");
   --  Create a new identifier for the program version of a
   --  subprogram.

   package Range_Axiom is new Name_Gen ("", Range_Name);
   --  From the name of an abstract type, return the name of
   --  its range axiom.

   package Range_Pred_Name is new Name_Gen ("", In_Range);
   --  From the name of an abstract type, return the name of
   --  its range predicate.

   package Record_Builder_Name is new Name_Gen (Record_Make, "");
   --  From the name of a record type, return the name of its builder.

   package Record_Getter_Axiom is new Name_Gen ("", Record_Get_Axiom);
   --  From the full name of a record component, return the name of
   --  its getter axiom.

   package Record_Getter_Name is new Name_Gen (Record_Get, "");
   --  From the full name of a record component, return the getter for
   --  this component.

   package Unicity_Axiom is new Name_Gen ("", Unicity);
   --  From the name of an abstract type, return the name of
   --  its unicity axiom.

end Why.Gen.Names;
