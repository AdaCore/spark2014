with P_14;
package body Q_14
   with Refined_State => (Q_State => Q_S)
is
   Q_S : Integer;

   procedure Init(S : out Integer)
   is
   begin
      S := 10;
   end Init;
begin
   P_14.Init(Q_S);
end Q_14;
