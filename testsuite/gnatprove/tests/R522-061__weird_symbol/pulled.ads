package Pulled is
   function F return Integer is (0) with SPARK_Mode => Off;
   subtype Q is Integer range 0 .. F;
end;
