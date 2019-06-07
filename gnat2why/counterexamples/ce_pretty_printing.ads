------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                   C E _ P R E T T Y _ P R I N T I N G                    --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                     Copyright (C) 2018-2019, AdaCore                     --
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
with SPARK_Atree.Entities;  use SPARK_Atree.Entities;
with Types;                 use Types;
with Urealp;                use Urealp;
with VC_Kinds;              use VC_Kinds;

package Ce_Pretty_Printing is

   function StringBits_To_Approx (Sign, Significand, Exp : String)
                                  return String;
   --  This function takes the three (sign, mantissa and exponent) string of
   --  bits representation output by prover and uses standard Ada float_io to
   --  output a decimal representation with 10 significant digits for 64bit
   --  float and 7 significant digits for 32 bits float.

   function Print_Fixed (Small : Ureal; Nb : String) return String;
   --  If the computation of Small * Nb is an integer we print it as an
   --  integer. If not, we print Nb * Num (Small) / Den (Small) with Small
   --  normalized Ureal.

   function Print_Float (Cnt_Value : Cntexmp_Value) return Unbounded_String
     with Pre => Cnt_Value.T = Cnt_Float;
   --  Print a counterexample value as a float

   generic
      --  This package is used to alter printing for values of Discrete_Type.
      --  When a value is close enough to the bounds of its type (Bound_Value
      --  close) and the type is not too small (Range greater than Bound_Type)
      --  then we print the value as a function of the bound of the type.
      --  Example:
      --  type Byte is range -128..127;
      --  V = - 127 is printed V = Byte'First + 1

      Bound_Type  : Int;
      Bound_Value : Int;
   package Gen_Print is

      function Print_Discrete (Nb : String; Nb_Type : Entity_Id) return String
        with Pre => Is_Discrete_Type (Nb_Type);

   end Gen_Print;

end Ce_Pretty_Printing;
