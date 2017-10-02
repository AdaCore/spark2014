with Byte_Types;
with System;

package Payload
  with SPARK_Mode => On
is

   Max_Payload_Size_In_Bytes : constant := 500;

   subtype Payload_Byte_Count is Byte_Types.Byte_Count
     range 0 .. Max_Payload_Size_In_Bytes;

   subtype Payload_Byte_Index is Payload_Byte_Count
     range 1 .. Payload_Byte_Count'Last;

   subtype Payload_Byte_Array is Byte_Types.Byte_Array (Payload_Byte_Index);



   type T is private;

   function Get_Packed_Payload (Data : T) return Byte_Types.Byte_Array;

private

   type T is
      record
         Payload : Payload_Byte_Array;
      end record;

end Payload;
