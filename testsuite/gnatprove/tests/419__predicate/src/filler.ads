generic
   Buffer_Bits            : in Long_Long_Integer;
   Buffer_Alignment_Bytes : in Long_Long_Integer := 4096; -- Page_Size;

package Filler
with SPARK_Mode => On
is

   pragma Warnings ("e");

   Used_Bytes    : constant Long_Long_Integer := Buffer_Bits / 8;
   Context_Bytes : constant Long_Long_Integer := ((Used_Bytes + Buffer_Alignment_Bytes - 1) / Buffer_Alignment_Bytes) * Buffer_Alignment_Bytes;
   Filler_Bytes  : constant Long_Long_Integer := Context_Bytes - Used_Bytes;

   pragma Assert (Filler_Bytes < Buffer_Alignment_Bytes);
   pragma Assert ((Used_Bytes + Filler_Bytes) mod Buffer_Alignment_Bytes = 0);

   type Byte is mod 2 ** 8;

   type Filler_Range is new Long_Long_Integer range 0 .. Filler_Bytes - 1;

   type Filler_Type is array (Filler_Range) of Byte;

end Filler;
