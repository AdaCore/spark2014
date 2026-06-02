------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                             C E _ V A L U E S                            --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                     Copyright (C) 2022-2026, AdaCore                     --
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

with Ada.Containers;
with Ada.Containers.Hashed_Maps;
with Ada.Containers.Ordered_Maps;
with Ada.Numerics.Big_Numbers.Big_Integers;
use Ada.Numerics.Big_Numbers.Big_Integers;
with Ada.Numerics.Big_Numbers.Big_Reals;
use Ada.Numerics.Big_Numbers.Big_Reals;
with Common_Containers;                     use Common_Containers;
with SPARK_Atree.Entities;                  use SPARK_Atree.Entities;
with Types;                                 use Types;

package CE_Values is

   type Float_Kind is (Float_32_K, Float_64_K, Extended_K);

   type Float_Value (K : Float_Kind := Float_32_K) is record
      case K is
         when Float_32_K =>
            Content_32 : Float;

         when Float_64_K =>
            Content_64 : Long_Float;

         when Extended_K =>
            Ext_Content : Long_Long_Float;
      end case;
   end record;

   function Mult_Fixed_Point
     (Fixed_L, Fixed_R : Big_Integer; Small_L, Small_R, Small_Res : Big_Real)
      return Big_Integer;
   --  Multiply two fixed-point numbers L and R and scale the result so that
   --  its small is equal to Small_Res

   function Div_Fixed_Point
     (Fixed_L, Fixed_R : Big_Integer; Small_L, Small_R, Small_Res : Big_Real)
      return Big_Integer;
   --  Divide two fixed-point numbers L and R and scale the result so that
   --  its small is equal to Small_Res

   function Is_Zero (R : Float_Value) return Boolean
   is (case R.K is
         when Float_32_K => R.Content_32 = 0.0,
         when Float_64_K => R.Content_64 = 0.0,
         when Extended_K => R.Ext_Content = 0.0);

   function Is_First (R : Float_Value) return Boolean
   is (case R.K is
         when Float_32_K => R.Content_32 = Float'First,
         when Float_64_K => R.Content_64 = Long_Float'First,
         when Extended_K => R.Ext_Content = Long_Long_Float'First);

   function Is_Last (R : Float_Value) return Boolean
   is (case R.K is
         when Float_32_K => R.Content_32 = Float'Last,
         when Float_64_K => R.Content_64 = Long_Float'Last,
         when Extended_K => R.Ext_Content = Long_Long_Float'Last);

   function Is_Valid (R : Float_Value) return Boolean;
   --  Return whether R is not NaN or -Inf or +Inf

   function To_Big_Integer (R : Float_Value) return Big_Integer;

   generic
      with function Oper_Float_32 (R : Float) return Float;
      with function Oper_Float_64 (R : Long_Float) return Long_Float;
      with
        function Oper_Float_Ext (R : Long_Long_Float) return Long_Long_Float;
   function Generic_Unop (R : Float_Value) return Float_Value;

   function Generic_Unop (R : Float_Value) return Float_Value
   is (case R.K is
         when Float_32_K => (Float_32_K, Oper_Float_32 (R.Content_32)),
         when Float_64_K => (Float_64_K, Oper_Float_64 (R.Content_64)),
         when Extended_K => (Extended_K, Oper_Float_Ext (R.Ext_Content)));

   function "-" is new Generic_Unop ("-", "-", "-");
   function "abs" is new Generic_Unop ("abs", "abs", "abs");
   function Succ is new
     Generic_Unop (Float'Succ, Long_Float'Succ, Long_Long_Float'Succ);
   function Pred is new
     Generic_Unop (Float'Pred, Long_Float'Pred, Long_Long_Float'Pred);

   generic
      with function Oper_Float_32 (L, R : Float) return Float;
      with function Oper_Float_64 (L, R : Long_Float) return Long_Float;
      with
        function Oper_Float_Ext
          (L, R : Long_Long_Float) return Long_Long_Float;
   function Generic_Binop (L, R : Float_Value) return Float_Value
   with Pre => L.K = R.K;

   function Generic_Binop (L, R : Float_Value) return Float_Value
   is (case L.K is
         when Float_32_K =>
           (Float_32_K, Oper_Float_32 (L.Content_32, R.Content_32)),
         when Float_64_K =>
           (Float_64_K, Oper_Float_64 (L.Content_64, R.Content_64)),
         when Extended_K =>
           (Extended_K, Oper_Float_Ext (L.Ext_Content, R.Ext_Content)));

   function "+" is new Generic_Binop ("+", "+", "+");
   function "-" is new Generic_Binop ("-", "-", "-");
   function "*" is new Generic_Binop ("*", "*", "*");
   function "/" is new Generic_Binop ("/", "/", "/");
   function Min is new
     Generic_Binop (Float'Min, Long_Float'Min, Long_Long_Float'Min);
   function Max is new
     Generic_Binop (Float'Max, Long_Float'Max, Long_Long_Float'Max);

   generic
      with function Compare_Float_32 (L, R : Float) return Boolean;
      with function Compare_Float_64 (L, R : Long_Float) return Boolean;
      with function Compare_Float_Ext (L, R : Long_Long_Float) return Boolean;
   function Generic_Compare (L, R : Float_Value) return Boolean
   with Pre => L.K = R.K;

   function Generic_Compare (L, R : Float_Value) return Boolean
   is (case L.K is
         when Float_32_K => Compare_Float_32 (L.Content_32, R.Content_32),
         when Float_64_K => Compare_Float_64 (L.Content_64, R.Content_64),
         when Extended_K => Compare_Float_Ext (L.Ext_Content, R.Ext_Content));

   function "<" is new Generic_Compare ("<", "<", "<");
   function "<=" is new Generic_Compare ("<=", "<=", "<=");
   function ">" is new Generic_Compare (">", ">", ">");
   function ">=" is new Generic_Compare (">=", ">=", ">=");

   function Conv_Real (Val : Float_Value; K : Float_Kind) return Float_Value
   is (case K is
         when Float_32_K =>
           (Float_32_K,
            (case Val.K is
               when Float_32_K => Val.Content_32,
               when Float_64_K => Float (Val.Content_64),
               when Extended_K => Float (Val.Ext_Content))),
         when Float_64_K =>
           (Float_64_K,
            (case Val.K is
               when Float_32_K => Long_Float (Val.Content_32),
               when Float_64_K => Val.Content_64,
               when Extended_K => Long_Float (Val.Ext_Content))),
         when Extended_K =>
           (Extended_K,
            (case Val.K is
               when Float_32_K => Long_Long_Float (Val.Content_32),
               when Float_64_K => Long_Long_Float (Val.Content_64),
               when Extended_K => Val.Ext_Content)));

   package Conv_Float32 is new Float_Conversions (Float);
   package Conv_Float64 is new Float_Conversions (Long_Float);

   function "=" (V1, V2 : Float_Value) return Boolean;
   --  Equality of floating point values

   function Copy_Sign is new
     Generic_Binop
       (Float'Copy_Sign,
        Long_Float'Copy_Sign,
        Long_Long_Float'Copy_Sign);

   type Scalar_Kind is (Integer_K, Enum_K, Char_K, Float_K, Fixed_K);
   --  Kind for a counterexample value for a scalar type

   type Scalar_Value_Type (K : Scalar_Kind := Integer_K) is record
      case K is
         when Integer_K =>
            Integer_Content : Big_Integer;

         when Enum_K =>
            Enum_Entity : Entity_Id;

         when Char_K =>
            Char_Node : Node_Id;

         when Float_K =>
            Float_Content : Float_Value;

         when Fixed_K =>
            Fixed_Content : Big_Integer;
            Small         : Big_Real;
      end case;
   end record;
   --  Representation of scalar counterexample values. Integers are represented
   --  as a big integer, enumerations as the entity of the corresponding
   --  literal, floating-point values as a floating point number of the
   --  appropriate size (32, 64, or extended), and fixed-point values as a big
   --  integer along with the small of their type as a big real.

   type Scalar_Value_Access is access Scalar_Value_Type;

   function "=" (V1, V2 : Scalar_Value_Type) return Boolean;
   --  Equality of scalar values

   type Value_Kind is (Scalar_K, Record_K, Array_K, Multidim_K, Access_K);
   --  The kind of counterexample values

   type Value_Type;

   type Value_Access is access Value_Type;

   function Default_Equal (V1, V2 : Value_Access) return Boolean renames "=";
   --  Rename the default equality operator before overriding it to avoid
   --  infinite recursive calls.

   function "=" (V1, V2 : Value_Type) return Boolean;
   --  Ada equality of two values

   function "=" (V1, V2 : Value_Access) return Boolean;
   --  Redefine equality for Value_Access based on equality for Value_Type

   package Entity_To_Value_Maps is new
     Ada.Containers.Hashed_Maps
       (Key_Type        => Entity_Id,
        Element_Type    => Value_Access,
        Hash            => Node_Hash,
        Equivalent_Keys => "=");
   --  Map entities to counterexample values. It is used for fields of a record
   --  value.

   package Big_Integer_To_Value_Maps is new
     Ada.Containers.Ordered_Maps
       (Key_Type     => Big_Integer,
        Element_Type => Value_Access);
   --  Values for a one-dimensional array. Keys may be integers or positions
   --  for enum values.

   type Opt_Boolean (Present : Boolean := False) is record
      case Present is
         when True =>
            Content : Boolean;

         when False =>
            null;
      end case;
   end record;

   type Opt_Big_Integer (Present : Boolean := False) is record
      case Present is
         when True =>
            Content : Big_Integer;

         when False =>
            null;
      end case;
   end record;

   subtype Supported_Dimensions is Positive range 1 .. 4;

   type Bound_Type is record
      First : Opt_Big_Integer;
      Last  : Opt_Big_Integer;
   end record;

   type Bound_Array is array (Natural range <>) of Bound_Type;
   type Multidim_Bounds (Dim : Supported_Dimensions := 1) is record
      Content : Bound_Array (1 .. Dim);
   end record;

   type Value_Type (K : Value_Kind := Scalar_K) is record
      AST_Ty : Entity_Id;

      case K is
         when Scalar_K =>
            Scalar_Content   : Scalar_Value_Access;
            Initialized_Attr : Opt_Boolean;
            Valid_Attr       : Opt_Boolean;

         when Record_K =>
            Record_Fields    : Entity_To_Value_Maps.Map;
            Constrained_Attr : Opt_Boolean;

         when Array_K =>
            First_Attr   : Opt_Big_Integer;
            Last_Attr    : Opt_Big_Integer;
            Array_Values : Big_Integer_To_Value_Maps.Map;
            Array_Others : Value_Access;

         when Multidim_K =>
            Bounds : Multidim_Bounds;

         when Access_K =>
            Designated_Value : Value_Access;
            Is_Null          : Opt_Boolean;
      end case;
   end record;
   --  Representation of a counterexample value.
   --  It can be of 5 different kinds:
   --  * Scalar values contains a scalar representation and optionally an
   --    initialization flag.
   --  * Array values are 1-dim array aggregates. They contain optional
   --    bounds, a map of associations of specific indexes to values, and
   --    an optional others value. Note that, if the index type is an
   --    enumeration, the indexes here are literals positions.
   --  * Record values are record aggregates. They contain mappings from
   --    components/discriminants to values and an optional boolean value
   --    for the constrained attribute if any.
   --  * Access values contain an Is_Null boolean flag and a designated value.
   --  * For multi-dimensional arrays, only store the bounds currently as no
   --    counterexample values can be supplied by the provers for their
   --    content.

   type Opt_Value_Type (Present : Boolean := False) is record
      case Present is
         when True =>
            Content : Value_Type;

         when False =>
            null;
      end case;
   end record;

   type Modifier is (None, Old, Loop_Entry, Result, Index);
   --  Used when the value given does not correspond to the value of the
   --  entity at this line but to the value of something else. This is only
   --  used for pretty printing and not RAC currently.
   --  Old and Loop_Entry correspond to values of the corresponding attributes.
   --  Index corresponds to the value of the underlying index for the
   --  quantified variable in a FOR OF array quantification.

   type Extended_Value_Access is array (Modifier) of Value_Access;

   package Entity_To_Extended_Value_Maps is new
     Ada.Containers.Hashed_Maps
       (Key_Type        => Entity_Id,
        Element_Type    => Extended_Value_Access,
        Hash            => Node_Hash,
        Equivalent_Keys => "=");
   --  Map entities to counterexample values extended with a modifier. This is
   --  used when parsing all counterexample values supplied for a line.

   function Get_Array_Length (V : Value_Type) return Opt_Big_Integer
   with Pre => V.K = Array_K;
   --  Return the length of the array if its first and last indices exist

   function Valid_Value (V : Value_Type) return Boolean
   with Ghost;
   --  A function to check in contracts and ghost code that the value V is
   --  well-formed. In particular, the following check has been currenty
   --  defined:
   --
   --  * If V is a record, then
   --    * Each key C_Key in the Record_Fields map must be compatible with
   --      V.AST_Ty in the sense that:
   --      * A component C_Ty is found in V.AST_Ty by searching for C_Key via
   --        Search_Component_In_Type and C_Key = C_Ty (i.e., the former isn't
   --    * The following exception is made for tagged types: Fields in the
   --      value are allowed to exist even when they do not exist in V.AST_Ty.
   --      This relaxation allows for handling values that are upcast to a type
   --      that might not contain such a field. (Note that erasing hidden
   --      fields from the value would prevent the proper treatment of a
   --      subsequent downcast.)
   --
   --  Note: To check values in the user's code the function Check_Value should
   --  be used instead.

   function Search_Component_In_Value
     (Rec : Value_Type; Comp : Entity_Id) return Entity_Id
   with
     Pre =>
       Rec.K = Record_K
       and Ekind (Comp) in E_Discriminant | E_Component | Type_Kind;
   --  Search among the component keys of the record value Rec for a key that
   --  corresponds to Comp in the type of the record value (its AST_Ty). If the
   --  corresponding key (component) is found it is returned. Otherwise, Empty
   --  is returned.

   procedure Update_Type (V : in out Value_Type; T_New : Entity_Id)
   with Pre => Ekind (T_New) in Type_Kind, Post => Valid_Value (V);
   --  Update the V.AST_Ty to New_Type. Adjust the structure of V if needed. It
   --  is assumed that the existing value is compatible with both types.
   --  However, the types could e.g. be different subtypes.

   function To_String (V : Float_Value) return String;
   --  Convert a float value to a string

   function To_String (V : Value_Type) return String;
   --  Debug printing for counterexample values

   function To_String (V : Opt_Value_Type) return String;

   type Supported_Attribute is (Initialized, First, Last, Constrained, Valid);
   --  Enumeration for attributes that are supported in the RAC.

   function To_String (Attribute : Supported_Attribute) return String;
   --  Convert supported attributes to a properly capitalized string (e.g.,
   --  "Initialized"). We can't simply use the Image attribute, as it would
   --  convert the attribute name to all upper case (e.g. "INITIALIZED").

end CE_Values;
