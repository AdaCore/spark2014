with Rule5_Proxy;

package body Rule5 is
   procedure Reinit is begin X := 0; end;
begin
   Rule5_Proxy;  --  @flow should say that Elaborate_Body must be added
end;
