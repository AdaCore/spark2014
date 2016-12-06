package Array_Component with SPARK_Mode is
   function Id (X : Integer) return Integer is (X);
   D : constant Integer := Id (0);
   type My_Array is array (Positive range <>) of
     Positive range D .. Integer'Last; --@RANGE_CHECK:FAIL
end Array_Component;
