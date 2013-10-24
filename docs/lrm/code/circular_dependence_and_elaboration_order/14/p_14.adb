with Q_14;
package body P_14
  with Refined_State => (P_State => P_S)
is
   P_S : Integer;

   procedure Init (S : out Integer) is
   begin
      S := 5;
   end Init;
begin
   Q_14.Init (P_S);
end P_14;
