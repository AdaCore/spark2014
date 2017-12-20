with Ada.Text_IO;

with Interfaces;

package body Output
with
   SPARK_Mode => Off
is

   procedure Print_Result (Value : Interfaces.Unsigned_64)
   is
   begin
      Ada.Text_IO.Put_Line (Value'Img);
   end Print_Result;

end Output;
