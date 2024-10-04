------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                   S P A R K _ U T I L - H A R D C O D E D                --
--                                                                          --
--                                  S p e c                                 --
--                                                                          --
--                     Copyright (C) 2020-2024, AdaCore                     --
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

   type Hardcoded_Enum is
     (Big_Integers,
      Big_Reals,
      Cut_Operations,
      Elementary_Functions,
      Real_Time,
      System_Storage_Elements,
      System
     );
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
   --  Big_Integers and Big_Integers_Ghost unit.
   --  Currently, the function to write a big integer to a string
   --  is left uninterpreted. The In_Range expression function is
   --  translated using the normal mechanism.

   package Big_Reals_Names is
      Big_Real             : constant String := "big_real";
      Is_Valid             : constant String := "is_valid";
      Min                  : constant String := "min";
      Max                  : constant String := "max";
      From_String          : constant String := "from_string";
      From_Universal_Image : constant String := "from_universal_image";
      From_Quotient_String : constant String := "from_quotient_string";
      Generic_To_Big_Real  : constant String := "to_big_real";
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

   package System_Storage_Elements_Names is
      To_Address : constant String := "to_address";
      To_Integer : constant String := "to_integer";
   end System_Storage_Elements_Names;
   --  Names of entities that will be considered hardcoded in the
   --  System.Storage_Elements unit.

   package Cut_Operations_Names is
      By : constant String := "by";
      So : constant String := "so";
   end Cut_Operations_Names;
   --  Names of entities that will be considered as hardcoded in the
   --  Cut_Operations unit.

   package Elementary_Functions_Names is
      Ada_Sqrt : constant String := "sqrt";
      Log      : constant String := "log";
      Exp      : constant String := "exp";
      Sin      : constant String := "sin";
      Cos      : constant String := "cos";
      Tan      : constant String := "tan";
      Cot      : constant String := "cot";
      Arcsin   : constant String := "arcsin";
      Arccos   : constant String := "arccos";
      Arctan   : constant String := "arctan";
      Arccot   : constant String := "arccot";
      Sinh     : constant String := "sinh";
      Cosh     : constant String := "cosh";
      Tanh     : constant String := "tanh";
      Coth     : constant String := "coth";
      Arcsinh  : constant String := "arcsinh";
      Arccosh  : constant String := "arccosh";
      Arctanh  : constant String := "arctanh";
      Arccoth  : constant String := "arccoth";
   end Elementary_Functions_Names;

   package Real_Time_Names is
      Time            : constant String := "time";
      Time_Span       : constant String := "time_span";
      Time_Unit       : constant String := "time_unit";
      Time_First      : constant String := "time_first";
      Time_Last       : constant String := "time_last";
      Time_Span_First : constant String := "time_span_first";
      Time_Span_Last  : constant String := "time_span_last";
      Time_Span_Zero  : constant String := "time_span_zero";
      Time_Span_Unit  : constant String := "time_span_unit";
      Nanoseconds     : constant String := "nanoseconds";
      Microseconds    : constant String := "microseconds";
      Milliseconds    : constant String := "milliseconds";
      Seconds         : constant String := "seconds";
      Minutes         : constant String := "minutes";
      To_Duration     : constant String := "to_duration";
      To_Time_Span    : constant String := "to_time_span";
      Time_Of         : constant String := "time_of";
      Split           : constant String := "split";
   end Real_Time_Names;

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
   --  Return True iff E is a hardcoded entity

   function Is_Literal_Function (E : Entity_Id) return Boolean with
     Post => (if Is_Literal_Function'Result then Is_Hardcoded_Entity (E));
   --  Return True iff E is a function used to encode literals. Those are
   --  handled specifically when they have string literals as parameters.

   function Get_Hardcoded_Unit (E : Entity_Id) return Hardcoded_Enum
     with Pre => Is_Hardcoded_Entity (E);
   --  Returns the unit in which the hardcoded entity E is defined

   function Has_Stoele_Offset (E : Type_Kind_Id) return Boolean;
   --  Return true if the entity is (a derived type of) the type
   --  System.Storage_Elements.Storage_Offset.

   function Is_System_Address (E : Type_Kind_Id) return Boolean;
   --  Return true if the entity is (a subtype of) the type
   --  System.Address;

   function Get_Real_Time_Time_Unit (E : Entity_Id) return Ureal with
     Pre => Is_From_Hardcoded_Unit (E, Real_Time);
   --  Return the value of Time_Unit from an entity of the package
   --  Ada.Real_Time.

end SPARK_Util.Hardcoded;
