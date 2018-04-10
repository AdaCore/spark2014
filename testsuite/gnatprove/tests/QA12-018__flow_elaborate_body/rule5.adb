with Rule5_Proxy1;
with Rule5_Proxy2;

package body Rule5 is
   procedure Reinit1 is begin X := 0; end;
   procedure Reinit2 is begin Y := 0; end;
begin
   Rule5_Proxy1;  --  @flow should say that Elaborate_Body must be added
   Rule5_Proxy2;  --  @flow should say that Elaborate_Body must be added
end;
