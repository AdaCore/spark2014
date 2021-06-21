with P.PC2.Q;
package body P.PC1.Q is
   procedure Proxy is
   begin
      P.PC2.Q.Me;
   end;
   procedure Me is
   begin
      X := 12345;
   end;
begin
   P.PC2.Q.Proxy;
end;
