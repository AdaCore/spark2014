package body Test is
   pragma SPARK_Mode(On);

   function Test (X : Integer) return Integer
   is
   begin
      --  Some counterexamples may be needed here
      if X = 0 then
         return 0;
      else
         return 1;
      end if;
   end Test;

end Test;
