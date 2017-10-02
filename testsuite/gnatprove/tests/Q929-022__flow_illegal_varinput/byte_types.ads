package Byte_Types
with SPARK_Mode => On
is

   type Byte is mod 2**8;
   for Byte'Size use 8;

   subtype Byte_Count is Natural;

   subtype Byte_Index is Byte_Count range 1 .. Byte_Count'Last;

   type Byte_Array is array (Byte_Index range <>) of Byte;
   pragma Pack (Byte_Array);

   Null_Byte_Array : constant Byte_Array (1 .. 0) := (others => 0);

end Byte_Types;
