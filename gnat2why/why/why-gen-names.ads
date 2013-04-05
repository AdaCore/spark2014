------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                        W H Y - G E N - N A M E S                         --
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

with Ada.Strings.Unbounded; use Ada.Strings.Unbounded;

with Namet;        use Namet;
with Snames;       use Snames;
with Types;        use Types;
with Uintp;        use Uintp;
with Why.Ids;      use Why.Ids;
with Why.Sinfo;    use Why.Sinfo;

with Why.Gen.Name_Gen;

package Why.Gen.Names is
   --  This package provides ways to manipulate subprogram names and
   --  to create identifiers from their string representation

   New_Temp_Identifier_Suffix : Unbounded_String;
   --  Suffix for all temporary names, so that the final name is
   --    _temp_<suffix>_<num>
   --  where <num> is a counter increased by one at each new temporary.

   function NID (Name : String) return Name_Id;
   --  Return Name_Id for Name

   function Conversion_Name
      (From : W_Base_Type_Id;
       To   : W_Base_Type_Id) return W_Identifier_Id;
   --  Return the name of the conversion function between the two types

   function Range_Pred_Name
     (Ty : Entity_Id) return W_Identifier_Id;
   --  Return the name of the "in_range" predicate for the type

   function Range_Check_Name
     (Ty : Entity_Id) return W_Identifier_Id;
   --  Return the name of the "range_check_" program function for the type

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

   function New_Exp (Kind : EW_Numeric) return W_Identifier_Id;
   --  Return the name of the exponential for the given kind

   function New_Abs (Kind : EW_Numeric) return W_Identifier_Id;
   --  Return the name of the absolute value operator for the given kind

   function New_Identifier (Ada_Node : Node_Id := Empty; Name : String)
       return W_Identifier_Id;
   --  Create a new term identifier for Name and return the result

   function New_Identifier (Ada_Node : Node_Id := Empty;
                            Name     : String;
                            Context  : String)
       return W_Identifier_Id;

   function New_Identifier
     (Ada_Node : Node_Id := Empty;
      Domain   : EW_Domain;
      Name     : String)
      return W_Identifier_Id;

   function New_Identifier
     (Ada_Node : Node_Id := Empty;
      Domain   : EW_Domain;
      Name     : String;
      Context  : String)
     return W_Identifier_Id;

   function New_Identifier
     (Ada_Node : Node_Id := Empty;
      Domain   : EW_Domain;
      Symbol   : Name_Id)
      return W_Identifier_Id;

   function New_Identifier
     (Ada_Node : Node_Id := Empty;
      Domain   : EW_Domain;
      Name     : String;
      Context  : Name_Id) return W_Identifier_Id;

   function New_Temp_Identifier return W_Identifier_Id;
   --  Return a new unique identifier

   function New_Temp_Identifiers (Num : Positive) return W_Identifier_Array;
   --  Return an array of new unique identifiers with Num elements

   function To_Exprs (Ids : W_Identifier_Array) return W_Expr_Array;
   --  Conversion each element of Ids to exprs and return the result

   function New_Str_Lit_Ident (N : Node_Id) return W_Identifier_Id;
   function New_Str_Lit_Ident (N : Node_Id) return String;
   --  Return a new unique identifier whose name only depends on the node that
   --  is passed

   function To_Program_Space (Name : W_Identifier_Id) return W_Identifier_Id;
   --  Create a new identifier for an entity in program space, given
   --  the name of the corresponding entity in logic space.

   type Why_Name_Enum is
     (
      WNE_Array_1,
      WNE_Array_2,
      WNE_Array_3,
      WNE_Array_4,
      WNE_Array_Access,
      WNE_Array_Elts,
      WNE_Array_First_Field,
      WNE_Array_Last_Field,
      WNE_Array_Offset,
      WNE_Array_Update,
      WNE_Attr_First,
      WNE_Attr_Image,
      WNE_Attr_Last,
      WNE_Attr_Length,
      WNE_Attr_Modulus,
      WNE_Attr_Value,
      WNE_Attr_Value_Pre_Check,
      WNE_Bool_And,
      WNE_Bool_Eq,
      WNE_Bool_Ge,
      WNE_Bool_Gt,
      WNE_Bool_Le,
      WNE_Bool_Lt,
      WNE_Bool_Ne,
      WNE_Bool_Or,
      WNE_Bool_Xor,
      WNE_Bool_Not,
      WNE_Char_Type,
      WNE_Coerce,
      WNE_Def,
      WNE_Def_Axiom,
      WNE_Dummy,
      WNE_Eq,

      --  suffix for the name of the theory defining the axiom for an
      --  expression function
      WNE_Expr_Fun_Axiom,

      --  suffix for the name of the theory importing all necessary axioms from
      --  other expression functions
      WNE_Expr_Fun_Closure,

      WNE_First_Static,
      WNE_Func,
      WNE_Ignore,
      WNE_Integer_Abs,
      WNE_Integer_Div,
      WNE_Integer_Exp,
      WNE_Integer_Mod,
      WNE_Integer_Rem,
      WNE_Integer_Max,
      WNE_Integer_Min,
      WNE_Keep_On_Simp,
      WNE_Last_Static,
      WNE_Of_Array,
      WNE_Of_Base,
      WNE_Of_Int,
      WNE_Of_Real,
      WNE_Range_Check_Fun,
      WNE_Pre_Check,
      WNE_Pretty_Ada,
      WNE_Private,
      WNE_Range_Axiom,
      WNE_Range_Field,
      WNE_Range_Pred,
      WNE_Range_Type,
      WNE_Real_Abs,
      WNE_Real_Ceil,
      WNE_Real_Div,
      WNE_Real_Exp,
      WNE_Real_Floor,
      WNE_Real_Of_Int,
      WNE_Real_Round,
      WNE_Real_Truncate,
      WNE_Result,
      WNE_Result_Exc,
      WNE_Sandbox,
      WNE_String,
      WNE_To_Array,
      WNE_To_Base,
      WNE_To_Int,
      WNE_To_Real,
      WNE_Type,
      WNE_Unicity
     );

   function Attr_To_Why_Name (A : Attribute_Id) return Why_Name_Enum;

   function Attr_To_Why_Name (A     : Attribute_Id;
                              Dim   : Pos;
                              Count : Positive) return W_Identifier_Id;

   function Attr_To_Why_Name (A     : Attribute_Id;
                              Dim   : Pos;
                              Count : Uint) return W_Identifier_Id;

   function Append_Num (S : String; Count : Positive) return W_Identifier_Id;

   function Append_Num (W : Why_Name_Enum; Count : Positive)
                        return W_Identifier_Id;

   function Append_Num (W : Why_Name_Enum; Count : Uint)
                        return W_Identifier_Id;

   function Append_Num (P, W : Why_Name_Enum; Count : Positive)
                        return W_Identifier_Id;

   function To_String (W : Why_Name_Enum) return String;

   function To_Ident (W        : Why_Name_Enum;
                      Ada_Node : Node_Id := Empty) return W_Identifier_Id;

   function Prefix (S        : String;
                    W        : Why_Name_Enum;
                    Ada_Node : Node_Id := Empty) return W_Identifier_Id;

   function Prefix (P        : String;
                    N        : String;
                    Ada_Node : Node_Id := Empty) return W_Identifier_Id;

   function Prefix (S        : Why_Name_Enum;
                    W        : Why_Name_Enum;
                    Ada_Node : Node_Id := Empty) return W_Identifier_Id;

   function Convert_To (Kind : EW_Basic_Type) return Why_Name_Enum
   with Pre => (Kind in EW_Int | EW_Real);

   function Convert_From (Kind : EW_Basic_Type) return Why_Name_Enum
   with Pre => (Kind in EW_Int | EW_Real);

   Array_Conv_Idemp         : constant String := "conv_idem";
   Array_Conv_Idemp_2       : constant String := "conv_idem_2";
   Assume                   : constant String := "assume";

   package New_Result_Temp_Identifier is
     new Name_Gen.Arity_1 (EW_Term, "", "result");
   --  Return a new identifier for the temporary used to store a function's
   --  result.

   package Assume_Name is
      new Name_Gen.Arity_1 (EW_Term, "", Assume);

   function Ada_Array_Name (Dimension : Pos) return Why_Name_Enum;

end Why.Gen.Names;
