with Ada.Text_IO; use Ada.Text_IO;
package body P2.Trace
  with SPARK_Mode => Off
is
   Put_Count : Natural := 0;

   procedure Put (S : String)
   is
   begin
      Put_Line (S);
      Put_Count := Put_Count + 1;
   end Put;

end P2.Trace;
