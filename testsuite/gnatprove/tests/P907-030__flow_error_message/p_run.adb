with P;
with Dp;

package body P_Run
with SPARK_Mode
is

   procedure Run is
      Y : Integer;
   begin
      P.Execute (X => Dp.Get_X,
                 Y => Y);
      Dp.Set_Y (Y => Y);
   end Run;

end P_Run;
