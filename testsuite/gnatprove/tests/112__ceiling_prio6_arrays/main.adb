with Proxy;

procedure Main with Priority => 4 is  --  @CEILING_PRIORITY_PROTOCOL:FAIL

begin
   Proxy.Proxy_Proc1;
   Proxy.Proxy_Proc2;
   Proxy.Proxy_Proc3;

end;
