with P;
procedure Main is
   function Proxy is new P.Generic_Proxy;
begin
   pragma Assert (Proxy = 0);
   pragma Assert (P.Unit.F (1) = 0);
end;
