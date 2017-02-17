package body Time is pragma SPARK_Mode (On);

   function T_Increment (X : T) return T is
      Result : T := X;
   begin
      if X.Seconds < Seconds_T'Last then
         Result.Seconds := Result.Seconds + 1;
         return Result;

      else
         Result.Seconds := 0;

         if X.Minutes < Minutes_T'Last then
            Result.Minutes := Result.Minutes + 1;
            return Result;

         else
            Result.Minutes := 0;
            Result.Hours := Result.Hours + 1;
            return Result;
         end if;
      end if;
   end T_Increment;

end Time;
