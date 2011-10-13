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

with Namet;        use Namet;
with Snames;       use Snames;
with Why.Ids;      use Why.Ids;
with Why.Sinfo;    use Why.Sinfo;

with Why.Gen.Name_Gen;

package Why.Gen.Names is
   --  This package provides ways to manipulate subprogram names and
   --  to create identifiers from their string representation

   function NID (Name : String) return Name_Id;
   --  Return Name_Id for Name

   function EW_Base_Type_Name (Kind : EW_Basic_Type) return String;
   --  Return the Why name of a base type (e.g. "int" for int)

   function New_Bool_Cmp
     (Rel       : EW_Relation;
      Arg_Types : W_Base_Type_Id)
     return W_Identifier_Id;
   --  Return the name of boolean comparison operators for Why term types
   --  in the domain EW_Term (i.e. the name of a logic function returning
   --  bool).

   function Why_Scalar_Type_Name (Kind : EW_Scalar) return String;
   --  Return the name of the Why scalar type (e.g. "real" from real)

   function New_Division (Kind : EW_Numeric) return W_Identifier_Id;
   --  Return the name of the division for the given kind

   function New_Abs (Kind : EW_Numeric) return W_Identifier_Id;
   --  Return the name of the absolute value operator for the given kind

   function New_Identifier (Name : String) return W_Identifier_Id;
   --  Create a new term identifier for Name and return the result

   function New_Identifier
     (Domain : EW_Domain;
      Name   : String)
     return W_Identifier_Id;
   --  Create a new identifier for Name and return the result

   function New_Term (Name : String) return W_Term_Id;
   --  Return a term identified by the given name

   function New_Prog (Name : String) return W_Prog_Id;
   --  Return a prog identified by the given name

   function New_Temp_Identifier return W_Identifier_Id;
   --  Create a new unique identifier and return the result

   function To_Program_Space (Name : W_Identifier_Id) return W_Identifier_Id;
   --  Create a new identifier for an entity in program space, given
   --  the name of the corresponding entity in logic space.

   Ada_Array                : constant String := "t__ada_array";
   Array_Access             : constant String := "access";
   Array_Update             : constant String := "update";
   Array_Equal              : constant String := "equal";
   Array_Convert_From       : constant String := "to_ada_array";
   Array_Convert_To         : constant String := "of_ada_array";
   Array_First_Static_Name  : constant String := "static_first";
   Array_Last_Static_Name   : constant String := "static_last";
   Array_Length_Static_Name : constant String := "static_length";
   Array_Conv_Idemp         : constant String := "conv_idem";
   Array_Conv_Idemp_2       : constant String := "conv_idem_2";
   Assume                   : constant String := "assume";
   Coerce                   : constant String := "coerce";
   Boolean_Eq               : constant String := "eq_bool";
   Eq_Pred                  : constant String := "eq";
   Of_Int                   : constant String := "of_int";
   Int_Of                   : constant String := "to_int";
   Definition               : constant String := "def";
   Logic_Def_Axiom          : constant String := "logic_def_axiom";
   Pre_Check                : constant String := "pre_check";
   Range_Name               : constant String := "range";
   In_Range                 : constant String := "in_range";
   Unicity                  : constant String := "unicity";
   Attr_First               : constant String :=
                                Attribute_Id'Image (Attribute_First);
   Attr_Last                : constant String :=
                                Attribute_Id'Image (Attribute_Last);
   Attr_Length              : constant String :=
                                Attribute_Id'Image (Attribute_Length);

   package Array_Access_Name is
     new Name_Gen.Arity_1 (EW_Term, "", Array_Access);
   --  From the name of an array type, return the name of its access function.

   package Array_Equal_Name is
     new Name_Gen.Arity_1 (EW_Term, "", Array_Equal);
   --  From the name of an array type, return the name of its equal function.

   package Array_Conv_To is
     new Name_Gen.Arity_1 (EW_Term, "", Array_Convert_To);
   --  From the name of an array type, return the name of the conversion from
   --  Ada__Array.

   package Array_Conv_From is
     new Name_Gen.Arity_1 (EW_Term, "", Array_Convert_From);
   --  From the name of an array type, return the name of the conversion to
   --  Ada__Array.

   package Array_Conv_Idem is
     new Name_Gen.Arity_1 (EW_Term, "", Array_Conv_Idemp);

   package Array_Conv_Idem_2 is
     new Name_Gen.Arity_1 (EW_Term, "", Array_Conv_Idemp_2);

   package Array_Update_Name is
     new Name_Gen.Arity_1 (EW_Term, "", Array_Update);
   --  From the name of an array type, return the name of its update function

   package Array_First_Static is
     new Name_Gen.Arity_1 (EW_Term, "", Array_First_Static_Name);
   --  From the name of an array type, return the name of the axiom that
   --  states that 'First is static.

   package Array_Last_Static is
     new Name_Gen.Arity_1 (EW_Term, "", Array_Last_Static_Name);
   --  From the name of an array type, return the name of the axiom that
   --  states that 'Last is static.

   package Array_Length_Static is
     new Name_Gen.Arity_1 (EW_Term, "", Array_Length_Static_Name);
   --  From the name of an array type, return the name of the axiom that
   --  states that 'Length is static.

   package Attr_Name is
     new Name_Gen.Arity_2 (EW_Term, "", "attr", "");
   --  From the prefix and the attribute, return the name of the corresponding
   --  logic function in Why.

   package Coerce_Axiom is
     new Name_Gen.Arity_1 (EW_Term, "", Coerce);
   --  From the name of an abstract type, return the name of
   --  its coerce axiom.

   package Conversion_To is
     new Name_Gen.Arity_2 (EW_Term, "", "to", "");
   --  From two type names, return the name of the logic function
   --  of the conversion from left to right.

   package Conversion_From is
     new Name_Gen.Arity_2 (EW_Term, "", "from", "");
   --  From two type names, return the name of the logic function
   --  of the conversion to left from right.

   package Eq_Param_Name is
     new Name_Gen.Arity_1 (EW_Prog, "", "___" & Boolean_Eq & "_", "");
   --  From the name of an abstract type, return the name of
   --  its equality parameter.

   package Eq_Pred_Name is
     new Name_Gen.Arity_1 (EW_Pred, "", Eq_Pred);
   --  From the name of an abstract type, return the name of
   --  its equality predicate.

   package Real_Of_Int is
     new Name_Gen.Arity_0 (EW_Term, "real_of_int");
   --  Return the name of the conversions from int to real

   package Int_Of_Bool is
     new Name_Gen.Arity_0 (EW_Term, "int_of_bool");
   --  Return the name of the conversions from int to real

   package New_Conversion_To_Int is
     new Name_Gen.Arity_1 (EW_Term, "", Int_Of);
   --  Create a new identifier for a conversion from an abstract type
   --  to int. The name of the abstract type is given in parameter.

   package New_Conversion_From_Int is
     new Name_Gen.Arity_1 (EW_Term, "", Of_Int);
   --  Create a new identifier for a conversion from int to an abstract type.
   --  The name of the abstract type is given in parameter.

   package New_Definition_Name is
     new Name_Gen.Arity_1 (EW_Prog, "", Definition);
   --  Create a new identifier for the "definition only" version of a
   --  subprogram, which is not meant to be called.

   package New_Exit_Identifier is
     new Name_Gen.Arity_0 (EW_Term, "Exit");
   --  Return an new identifier for the exception "Exit".

   package New_Ignore_Name is
     new Name_Gen.Arity_0 (EW_Term, "___ignore");

   package New_Integer_Division is
     new Name_Gen.Arity_0 (EW_Term, "computer_div");
   --  Return an identifier that corresponds to integer division in Why

   package New_Real_Division is
     new Name_Gen.Arity_0 (EW_Term, "div_real");
   --  Return an identifier that corresponds to real division in Why

   package New_Integer_Abs is
     new Name_Gen.Arity_0 (EW_Term, "abs_int");
   --  Return an identifier that corresponds to integer abs in Why

   package New_Real_Abs is
     new Name_Gen.Arity_0 (EW_Term, "AbsReal.abs");
   --  Return an identifier that corresponds to real abs in Why

   package New_Result_Exc_Identifier is
     new Name_Gen.Arity_0 (EW_Prog, "_result_exc");
   --  Return a new identifier for the exception used for returning from a
   --  subprogram.

   package New_Result_Identifier is
     new Name_Gen.Arity_0 (EW_Term, "result");
   --  Return a new identifier for a function result as it
   --  would be used into a postcondition.

   package New_Result_Temp_Identifier is
     new Name_Gen.Arity_1 (EW_Term, "", "result");
   --  Return a new identifier for the temporary used to store a function's
   --  result.

   package New_Conversion_Axiom is
     new Name_Gen.Arity_2 (EW_Term, "", "of", "in_range");
   --  Create a new identifier for a conversion between to abstract types

   package Logic_Func_Name is
     new Name_Gen.Arity_1 (EW_Term, "", "", "");
   --  Create a new identifier for the logic version of a
   --  subprogram, which is used in annotations.

   package Logic_Func_Axiom is
     new Name_Gen.Arity_1 (EW_Term, "", Logic_Def_Axiom);
   --  Create a new name for the axiom that states equivalence of
   --  a subprogram and its logic definition.

   package Mod_Name is
     new Name_Gen.Arity_0 (EW_Term, "math_mod");

   package New_Pre_Check_Name is
     new Name_Gen.Arity_1 (EW_Prog, Pre_Check, "");
   --  Return an identifier for the subprogram that checks whether a
   --  precondition is properly guarded

   package Program_Func_Name is
     new Name_Gen.Arity_1 (EW_Prog, "", "_", "");
   --  Create a new identifier for the program version of a
   --  subprogram.

   package Range_Axiom is
     new Name_Gen.Arity_1 (EW_Term, "", Range_Name);
   --  From the name of an abstract type, return the name of
   --  its range axiom.

   package Range_Pred_Name is
     new Name_Gen.Arity_1 (EW_Pred, "", In_Range);
   --  From the name of an abstract type, return the name of
   --  its range predicate.

   package Range_Check_Name is
     new Name_Gen.Arity_1 (EW_Prog, "", In_Range & "_");
   --  From the name of an abstract type, return the name of
   --  its range check.

   package Unicity_Axiom is
     new Name_Gen.Arity_1 (EW_Term, "", Unicity);
   --  From the name of an abstract type, return the name of
   --  its unicity axiom.

   package Assume_Name is
      new Name_Gen.Arity_1 (EW_Term, "", Assume);
end Why.Gen.Names;
