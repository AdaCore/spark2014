with Interfaces;
with System;

package Types
with SPARK_Mode
is

   use type Interfaces.Integer_64;

   type Data_Type is new Integer
   with Size => 32;

   type Data_Range is new Interfaces.Integer_64 range 0 .. 2 ** 60 - 1;
   subtype Data_Count is Data_Range;

   type Buffer_Range is range 1 .. 4095;

   subtype Buffer_Address_Type is System.Address
   with Predicate => Buffer_Address_Type mod Types.Data_Type'Alignment = 0;

   type Buffer_Type is record
      Base_Address : Buffer_Address_Type;
      Base_Index   : Data_Range;
      First        : Data_Range;
   end record;

   type Buffer_Array is array (Buffer_Range range <>) of Buffer_Type;

end Types;
