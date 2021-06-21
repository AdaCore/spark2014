with P.PC1.Q;
package body P.PC2.Q is
   procedure Proxy is
   begin
      P.PC1.Q.Me;
   end;
   procedure Me is
   begin
      Y := 12345;
   end;
begin
   P.PC1.Q.Proxy;
end;
