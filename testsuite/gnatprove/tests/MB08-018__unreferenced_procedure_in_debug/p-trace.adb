with Ada.Text_IO; use Ada.Text_IO;
separate (P)
package body Trace
  with SPARK_Mode => Off
is

   procedure Print_Log (S : in String)
   is
   begin
      Put_Line (S);
   end Print_Log;

end Trace;

