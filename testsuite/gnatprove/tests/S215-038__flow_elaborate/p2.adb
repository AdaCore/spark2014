with Proxy;

package body P2
  with Refined_State => (State => Hidden_Var)
is
   Hidden_Var : Integer;

   procedure Dummy is null;
begin
   Hidden_Var := Proxy;
   --  this call reads P.State, which isn't known to be elaborated
end P2;
