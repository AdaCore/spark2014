------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                             C E _ V A L U E S                            --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                     Copyright (C) 2022-2022, AdaCore                     --
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
with Common_Containers;        use Common_Containers;
with Types;                    use Types;

package CE_Values is

   type Float_Kind is (Float_32_K, Float_64_K, Extended_K);

   type Float_Value (K : Float_Kind := Float_32_K) is record
      case K is
         when Float_32_K =>
            Content_32  : Float;
         when Float_64_K =>
            Content_64  : Long_Float;
         when Extended_K =>
            Ext_Content : Long_Long_Float;
      end case;
   end record;

   type Scalar_Kind is (Integer_K, Enum_K, Float_K, Fixed_K);
   --  Kind for a counterexample value for a scalar type

   type Scalar_Value_Type (K : Scalar_Kind := Integer_K) is record
      case K is
         when Integer_K =>
            Integer_Content : Big_Integer;
         when Enum_K =>
            Enum_Entity     : Entity_Id;
         when Float_K =>
            Float_Content   : Float_Value;
         when Fixed_K =>
            Fixed_Content   : Big_Integer;
            Small           : Big_Real;
      end case;
   end record;
   --  Representation of scalar counterexample values. Integers are represented
   --  as a big integer, enumerations as the entity of the corresponding
   --  literal, floating-point values as a floating point number of the
   --  appropriate size (32, 64, or extended), and fixed-point values as a big
   --  integer along with the small of their type as a big real.

   type Scalar_Value_Access is access Scalar_Value_Type;

   type Value_Kind is (Scalar_K, Record_K, Array_K, Multidim_K, Access_K);
   --  The kind of counterexample values

   type Value_Type;

   type Value_Access is access Value_Type;

   package Entity_To_Value_Maps is new Ada.Containers.Hashed_Maps
     (Key_Type        => Entity_Id,
      Element_Type    => Value_Access,
      Hash            => Node_Hash,
      Equivalent_Keys => "=");
   --  Map entities to counterexample values. It is used for fields of a record
   --  value.

   package Big_Integer_To_Value_Maps is new Ada.Containers.Ordered_Maps
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
         when Scalar_K   =>
            Scalar_Content   : Scalar_Value_Access;
            Initialized_Attr : Opt_Boolean;
         when Record_K   =>
            Record_Fields    : Entity_To_Value_Maps.Map;
            Constrained_Attr : Opt_Boolean;
         when Array_K    =>
            First_Attr       : Opt_Big_Integer;
            Last_Attr        : Opt_Big_Integer;
            Array_Values     : Big_Integer_To_Value_Maps.Map;
            Array_Others     : Value_Access;
         when Multidim_K =>
            Bounds           : Multidim_Bounds;
         when Access_K   =>
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

   package Entity_To_Extended_Value_Maps is new Ada.Containers.Hashed_Maps
     (Key_Type        => Entity_Id,
      Element_Type    => Extended_Value_Access,
      Hash            => Node_Hash,
      Equivalent_Keys => "=");
   --  Map entities to counterexample values extended with a modifier. This is
   --  used when parsing all counterexample values supplied for a line.

   function Get_Array_Elt
      (V : Value_Type;
       J : Positive) return Value_Access;
   --  Retrieve value of V at index J - 1

   function Get_Array_Length (V : Value_Type) return Opt_Big_Integer
   with
       Pre => V.K = Array_K;
   --  Return the length of the array if its first and last indices exist

   function To_String (V : Value_Type) return String;
   --  Debug printing for counterexample values

   function To_String (V : Opt_Value_Type) return String;

end CE_Values;
