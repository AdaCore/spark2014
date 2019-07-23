with P_05;
package body Q_05
is
   Q_State : Integer;

   procedure Init(S : out Integer)
   is
   begin
      S := 10;
   end Init;
begin
   P_05.Init(Q_State);
end Q_05;
