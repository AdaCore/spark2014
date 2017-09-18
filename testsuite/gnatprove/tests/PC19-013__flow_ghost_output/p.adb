with Proxy; pragma Elaborate_All (Proxy);

package body P is

   procedure Init is
   begin
      X := True;
   end;

begin
   Proxy;
end;
