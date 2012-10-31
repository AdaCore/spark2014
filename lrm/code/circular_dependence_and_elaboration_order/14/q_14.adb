with P_14;
package body Q_14
is
   Q_State : Integer;
   
   procedure Init(S : out Integer)
   is
   begin
      S := 10;
   end Init;
begin
   P_14.Init(Q_State);
end Q_14;
