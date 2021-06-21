with P.C;
package body P with Refined_State => (State => (P.C.X, Y)) is
   procedure Init_Y is
   begin
      Y := 0;
   end;
begin
   P.C.Proxy;
end;
