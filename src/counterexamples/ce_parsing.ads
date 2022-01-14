------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                            C E _ P A R S I N G                           --
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

with Ada.Numerics.Big_Numbers.Big_Reals;
use Ada.Numerics.Big_Numbers.Big_Reals;
with Ada.Numerics.Big_Numbers.Big_Integers;
use Ada.Numerics.Big_Numbers.Big_Integers;
with SPARK_Atree.Entities;     use SPARK_Atree.Entities;
with Types;                    use Types;
with VC_Kinds;                 use VC_Kinds;

package CE_Parsing is

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

   type Scalar_Value (K : Scalar_Kind := Integer_K) is record
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

   Parse_Error : exception;

   function Parse_Scalar_Value
     (Cnt_Value : Cntexmp_Value_Ptr;
      AST_Type  : Entity_Id) return Scalar_Value
   with Pre => Is_Scalar_Type (AST_Type);
   --  Parse a counterexample value as a value of AST_Type. If it cannot be
   --  parsed that way, Parse_Error is raised.

end CE_Parsing;
