package Array_Component with SPARK_Mode is
   function Id (X : Integer) return Integer is (X);
   D : constant Integer := Id (0);
   type My_Array is array (Positive range <>) of --@RANGE_CHECK:FAIL
     Positive range D .. Integer'Last;

   subtype S is My_Array (1 .. 2);  --@RANGE_CHECK:NONE
   type T is new My_Array (1 .. 2);  --@RANGE_CHECK:NONE
end Array_Component;
