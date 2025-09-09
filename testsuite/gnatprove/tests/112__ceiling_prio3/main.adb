with Proxy;
with Prots2;

procedure Main is  --  @CEILING_PRIORITY_PROTOCOL:FAIL
   pragma Priority (5);

begin
   Proxy.Proc1;
   Proxy.Proc2;
   Proxy.Proc3;

end Main;
