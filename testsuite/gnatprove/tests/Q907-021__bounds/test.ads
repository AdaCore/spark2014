package Test
  with SPARK_Mode => On
is

   type Byte is mod 2**8;
   for Byte'Size use 8;

   subtype Byte_Count is Natural;

   subtype Byte_Index is Byte_Count range 1 .. Byte_Count'Last;

   type Byte_Array is array (Byte_Index range <>) of Byte;

   pragma Pack (Byte_Array);



   Max_Payload_Size_In_Bytes : constant := 100;

   subtype Payload_Byte_Count is Byte_Count range 0 .. Max_Payload_Size_In_Bytes;

   subtype Payload_Byte_Index is Payload_Byte_Count range 1 .. Payload_Byte_Count'Last;

   subtype Payload_Byte_Array is Byte_Array (Payload_Byte_Index);


   function Serialize return Byte_Array;


end Test;
