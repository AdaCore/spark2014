package body protectedFloat is pragma SPARK_Mode (On);

   pragma Validity_Checks (All_Checks);

   function protectedRealDivide( left, right : in Real) return Real
   is
   begin
      -- Check for fractional denominator
      if right < 1.0 then
         -- Guard against divide by zero
         if right = 0.0 then
            return Real'Last;
         -- Guard against overflow where left/right > Real'Last
         elsif right < (left/Real'Last ) then
            return Real'Last;
         else
            return left/right;
         end if;
      else
         return left/right;
      end if;
   end protectedRealDivide;

end protectedFloat;
