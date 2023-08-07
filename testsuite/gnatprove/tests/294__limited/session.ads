with GNAT.Sockets;

with RFLX.DHCP_Client.Session;

package Session with
  SPARK_Mode
is

   type Context is new RFLX.DHCP_Client.Session.Context with
      record
         Socket : GNAT.Sockets.Socket_Type;
      end record;

end Session;
