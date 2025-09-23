with Proxy;
with Tasks1;
with Tasks2;

procedure Main is  --  @CEILING_PRIORITY_PROTOCOL:FAIL
   pragma Priority (5);

begin
   Proxy.Proxy_Proc1;
   Proxy.Proxy_Proc2;

end Main;
