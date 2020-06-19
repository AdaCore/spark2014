package FP with SPARK_Mode is

   subtype Fixed is Duration range 0.0 .. 5.0 - Duration'Small;

   subtype Int is Integer range 0 .. 4;

   function Floor (F : Fixed) return Int is
     (if F = 0.0 then 0 else Int (F - 0.5));  -- @RANGE_CHECK:PASS

end;
