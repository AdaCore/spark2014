pragma SPARK_Mode;
function Where_Are_The_Run_Time_Errors ( Input : Integer) return Integer is
   X, Y, K : Integer;
begin
   K := Input / 100;
   X := 2;
   Y := K + 5;
   while X < 10 loop
      Y := Y + 3;
      X := X + 1;
      pragma Loop_Invariant (Y = Y'Loop_Entry + 3 * (X - 2));-- 3 * (X - 2)
      pragma Loop_Invariant (X >= 3);
   end loop;

   if (3 * K + 100) > 43 then
      Y := Y + 1;
      X := X / (X - Y);
   end if;
   return X;
end Where_Are_The_Run_Time_Errors;
