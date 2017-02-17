-- Comment out with context clause, and all is well!
with Ada.Text_IO;

separate (Skein)
package body Trace
  with SPARK_Mode => Off
is

   procedure Set_Flags (F : in out Integer) is
   begin
      F := F + 1;
   end Set_Flags;

end Trace;

