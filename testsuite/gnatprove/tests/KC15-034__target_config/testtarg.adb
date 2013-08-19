with System; use System;
with Interfaces.C; use Interfaces.C;
procedure TestTarg is
begin
   pragma Assert (wchar_t'Size = 32);
   pragma Assert (Long_Long_Integer'Size = 64);
   pragma Assert (Float'Size = 32);
   pragma Assert (Long_Float'Size = 64);
end;
