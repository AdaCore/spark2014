with Ada.Text_IO;
package body Warnings
  with SPARK_Mode
is
   procedure P1 is
   begin
      null;
   end P1;

   procedure P2 is
   begin
      Ada.Text_IO.Put_Line ("bla");
   end P2;

end Warnings;
