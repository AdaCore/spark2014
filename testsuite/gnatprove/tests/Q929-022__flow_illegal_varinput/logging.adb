with Ada.Unchecked_Conversion;
with Byte_Types;


package body Logging
  with SPARK_Mode => On
is

   procedure Log_Payload (Data : in Payload.T)
   is

      Payload_As_Bytes : Byte_Types.Byte_Array :=
        Payload.Get_Packed_Payload (Data);

      subtype Payload_As_String_Index is Positive range
        1 .. Payload_As_Bytes'Length;

      subtype Payload_As_String_T is String (Payload_As_String_Index);

      function Bytes_To_String is new Ada.Unchecked_Conversion
        (Source => Byte_Types.Byte_Array,
         Target => Payload_As_String_T);

   begin

      null;

   end Log_Payload;


end Logging;
