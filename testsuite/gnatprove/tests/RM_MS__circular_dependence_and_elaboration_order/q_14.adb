with P_14;
pragma Elaborate_All (P_14); -- Required because the elaboration of the
                             -- body of Q_14 (indirectly) calls P_14.Init
package body Q_14
  with SPARK_Mode,
       Refined_State => (Q_State => Q_S)
is
   Q_S : T;

   procedure Init (S : out T) is
      V : Integer;
   begin
      P_14.Init (V);
      if V > 0 and then  V <= Integer'Last - 5 then
         S := T(V + 5);
      else
         S := 5;
      end if;
   end Init;
begin
   Init (Q_S);
end Q_14;
