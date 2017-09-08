
with Test; use Test;

procedure Main
  with SPARK_Mode => On
is

   procedure Copy_To_Buffer (Payload       : in     Byte_Array;
                             Payload_Bytes : in out Payload_Byte_Array)
   is
   begin
      Payload_Bytes (Payload'Range) := Payload; --@LENGTH_CHECK:FAIL
   end Copy_To_Buffer;

   Payload_Bytes : Payload_Byte_Array := (others => 0);

begin
   Copy_To_Buffer (Payload       => Serialize,
                   Payload_Bytes => Payload_Bytes);
end Main;
