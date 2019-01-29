with Q_05;
package body P_05
is
   P_State : Integer;

   procedure Init(S : out Integer)
   is
   begin
      S := 5;
   end Init;
begin
   Q_05.Init(P_State);
end P_05;
