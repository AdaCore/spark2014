package body Skein
   with SPARK_Mode
is
   pragma Assertion_Policy (Assert => Check);

   package Trace
     with SPARK_Mode => On
   is
      procedure Set_Flags (F : in out Integer);
   end Trace;

   -- Following this stub, all analysis seems to stop!
   package body Trace is separate;

   procedure Set_Flags (F : in out Integer) is
   begin
      F := F + 1;
   end Set_Flags;
end Skein;
