------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                   S P A R K _ U T I L - H A R D C O D E D                --
--                                                                          --
--                                  S p e c                                 --
--                                                                          --
--                     Copyright (C) 2020-2020, AdaCore                     --
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

   type Hardcoded_Enum is (Big_Integers);
   --  Enum type of the hardcoded units

   package Big_Integers_Names is
      Big_Integer              : constant String := "big_integer";
      Is_Valid                 : constant String := "is_valid";
      To_Big_Integer           : constant String := "to_big_integer";
      In_Range                 : constant String := "in_range";
      To_Integer               : constant String := "to_integer";
      Min                      : constant String := "min";
      Max                      : constant String := "max";
      Gcd                      : constant String := "greatest_common_divisor";
      Generic_To_Big_Integer   : constant String := "to_big_integer";
      Generic_From_Big_Integer : constant String := "from_big_integer";
   end Big_Integers_Names;
   --  Names of entities that will be considered as hardcoded in the
   --  Big_Integers unit.

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
