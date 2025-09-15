with Proxy;

procedure Main is  --  @CEILING_PRIORITY_PROTOCOL:FAIL
   pragma Priority (3);

begin
   Proxy.Proc1;
   Proxy.Proc2;
   Proxy.Proc3;

end Main;
