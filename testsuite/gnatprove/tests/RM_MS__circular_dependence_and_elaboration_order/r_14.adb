with Q_14;
pragma Elaborate_All (Q_14); -- Required because Q_14.Init is called
                             -- in the elaboration of the body of R_14
use type Q_14.T;

package body R_14
  with SPARK_Mode,
       Refined_State => (State => R_S)
is
   R_S : Q_14.T;
   procedure Op ( X : in Positive)
     with Refined_Global => (In_Out => R_S)
   is
   begin
      if R_S <= Q_14.T'Last - Q_14.T (X) then
         R_S := R_S + Q_14.T (X);
      else
         R_S := 0;
      end if;
   end Op;
begin
   Q_14.Init (R_S);
   if P_14.Global_Var > 0
     and then R_S <= Q_14.T'Last - Q_14.T (P_14.Global_Var)
   then
      R_S := R_S + Q_14.T (P_14.Global_Var);
   else
      R_S := Q_14.T (P_14.Global_Var);
   end if;
end R_14;
