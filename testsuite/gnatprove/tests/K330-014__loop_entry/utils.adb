package body Utils is pragma SPARK_Mode (On);

   ------------
   -- Sum_Of --
   ------------

   function Sum_Of (Val : Natural) return Natural is
   begin
      if Val > 0 then
         return Sum_Of (Val - 1) + Val;
      else
         return 0;
      end if;
   end Sum_Of;

end Utils;
