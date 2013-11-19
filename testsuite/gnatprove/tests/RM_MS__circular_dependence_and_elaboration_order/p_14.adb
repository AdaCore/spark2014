with Q_14;

package body P_14
  with SPARK_Mode,
       Refined_State => (P_State => P_S)
is
   P_S : Q_14.T;  -- The use of type Q.T does not require
                  -- the body of Q to be elaborated.

   procedure Init (S : out Integer) is
   begin
      S := 5;
   end Init;
begin
   -- Cannot call Q_14.Init here beacuse
   -- this would require an Elaborate_All for Q_14
   -- and would be detected as a circularity
   Init (Global_Var);
   P_S := Q_14.T (Global_Var);
end P_14;
