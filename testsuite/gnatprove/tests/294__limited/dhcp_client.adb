pragma SPARK_Mode;

with RFLX.DHCP_Client.Session;

with Session;

procedure DHCP_Client is
   package DHCP_Client_Session renames RFLX.DHCP_Client.Session;

   Ctx : Session.Context;
begin
   DHCP_Client_Session.Initialize (Ctx);
end DHCP_Client;
