------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                    G N A T 2 W H Y _ C E _ F U Z Z E R                   --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                       Copyright (C) 2022, AdaCore                        --
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

with Ada.Numerics.Big_Numbers.Big_Integers;
use  Ada.Numerics.Big_Numbers.Big_Integers;
with CE_Values;   use CE_Values;
with Einfo.Utils; use Einfo.Utils;
with Types;       use Types;

package CE_Fuzzer is

   function Fuzz_Integer_Value (Ty : Entity_Id) return Value_Type
     with Pre => Is_Integer_Type (Ty);
   --  Return a Value_Type in the range of the Rep_Ty type randomly chosen
   --  among a set of values known to often lead to errors.

   function Fuzz_Record_Value (Ty : Entity_Id) return Value_Type
     with Pre => Is_Record_Type (Ty);
   --  Return a Value_Type of record kind with fields filled with fuzzed
   --  values.

end CE_Fuzzer;
