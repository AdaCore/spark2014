package Scalar_Types with SPARK_Mode is

   function Id (X : Integer) return Integer is (X);

   type Dyn_Ty is new Integer range 1 .. Id (10);

   type Stat_Ty is new Dyn_Ty range 1 .. 100; --@RANGE_CHECK:FAIL

end Scalar_Types;
