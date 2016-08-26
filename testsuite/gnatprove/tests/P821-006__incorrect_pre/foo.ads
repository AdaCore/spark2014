with Ada.Unchecked_Conversion;
with Interfaces; use Interfaces;

package foo with SPARK_Mode is

   type Byte is mod 2**8;
   type Byte_Array is array (Natural range <>) of Byte;
   type Byte_Array_4 is array (1..4) of Byte;

   subtype Data_Type is Byte_Array; -- essential

   function From_Byte_Array_To_Integer_32 is new
     Ada.Unchecked_Conversion (Source => Byte_Array_4,
                               Target => Integer_32);

   function toInteger_32 (bytes : Byte_Array) return Integer_32
   is (From_Byte_Array_To_Integer_32 (Byte_Array_4 (bytes)))
   with Pre => bytes'Length = 4;

end foo;
