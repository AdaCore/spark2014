------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                   S P A R K _ U T I L - H A R D C O D E D                --
--                                                                          --
--                                  S p e c                                 --
--                                                                          --
--                     Copyright (C) 2020-2021, AdaCore                     --
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

package SPARK_Util.Hardcoded is

   type Hardcoded_Enum is (Big_Integers, Big_Reals);
   --  Enum type of the hardcoded units

   package Big_Integers_Names is
      Big_Integer              : constant String := "big_integer";
      Is_Valid                 : constant String := "is_valid";
      To_Big_Integer           : constant String := "to_big_integer";
      To_Integer               : constant String := "to_integer";
      Min                      : constant String := "min";
      Max                      : constant String := "max";
      Gcd                      : constant String := "greatest_common_divisor";
      From_String              : constant String := "from_string";
      Generic_To_Big_Integer   : constant String := "to_big_integer";
      Generic_From_Big_Integer : constant String := "from_big_integer";
   end Big_Integers_Names;
   --  Names of entities that will be considered as hardcoded in the
   --  Big_Integers unit.
   --  Currently, the function to write a big integer to a string
   --  is left uninterpreted. The In_Range expression function is
   --  translated using the normal mechanism.

   package Big_Reals_Names is
      Big_Real              : constant String := "big_real";
      Is_Valid              : constant String := "is_valid";
      Min                   : constant String := "min";
      Max                   : constant String := "max";
      From_String           : constant String := "from_string";
      Generic_To_Big_Real   : constant String := "to_big_real";
   end Big_Reals_Names;
   --  Names of entities that will be considered as hardcoded in the
   --  Big_Reals unit.
   --  Currently, the function to write a big real to a string,
   --  as well as the numerator and denominator functions are left
   --  uninterpreted. Expression functions To_Real and To_Big_Real as well as
   --  In_Range are translated using the normal mechanism.
   --  Conversions to a fixed or floating point type from a big real are also
   --  left uninterpreted. However, because they have a precondition featuring
   --  a raise expression, they are not currently supported in SPARK.

   function Is_From_Hardcoded_Unit
     (E    : Entity_Id;
      Unit : Hardcoded_Enum)
      return Boolean;
   --  Returns True iff E is from the hardcoded unit corresponding to Unit

   function Is_From_Hardcoded_Generic_Unit
     (E    : Entity_Id;
      Unit : Hardcoded_Enum)
      return Boolean;
   --  Returns True iff E is from a generic unit defined in the hardcoded unit
   --  corresponding to Unit.

   function Is_Hardcoded_Entity (E : Entity_Id) return Boolean;
   --  Return True iff E is a hardcoded entity.

   function Get_Hardcoded_Unit (E : Entity_Id) return Hardcoded_Enum
     with Pre => Is_Hardcoded_Entity (E);
   --  Returns the unit in which the hardcoded entity E is defined

end SPARK_Util.Hardcoded;
