with Q_14;
package body P_14
is
   P_State : Integer;
   
   procedure Init(S : out Integer)
   is
   begin
      S := 5;
   end Init;
begin
   Q_14.Init(P_State);
end P_14;
