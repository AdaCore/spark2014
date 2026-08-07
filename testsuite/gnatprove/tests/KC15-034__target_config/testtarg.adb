with System;       use System;
with Interfaces.C; use Interfaces.C;

procedure TestTarg is
   pragma SPARK_Mode (On);
begin
   --  Integer'Size and wchar_t'Size differ from the corresponding values of
   --  all native targets we test on, so these assertions only hold when the
   --  target configuration file is really taken into account.

   pragma Assert (Integer'Size = 64);
   pragma Assert (wchar_t'Size = 32);
   pragma Assert (Long_Long_Integer'Size = 64);
   pragma Assert (Float'Size = 32);
   pragma Assert (Long_Float'Size = 64);
end;
