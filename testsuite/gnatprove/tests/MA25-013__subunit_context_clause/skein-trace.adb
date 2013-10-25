-- Comment out with context clause, and all is well!
with Ada.Text_IO;

separate (Skein)
package body Trace
  with SPARK_Mode => Off
is

   Flags : Skein.Debug_Flag_Set := Skein.Debug_None;

   procedure Set_Flags (F : in Debug_Flag_Set)
   is
   begin
      Flags := F;
   end Set_Flags;

end Trace;

