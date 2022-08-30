with Ada.Text_IO;
package body Test
with Spark_Mode => On
is

   procedure Wrong is
      function Get return Nibble is (1);
      Dummy : constant Nibble := not Get;
   begin
      Ada.Text_IO.Put_Line (Nibble'Image (Dummy));
      null;
   end Wrong;
end Test;
