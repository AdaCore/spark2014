package Mod_Array with SPARK_mode is
   type My_Index is mod 2 ** 64;

   type A is array (My_Index range <>) of Boolean with Pack;

   function My_Length (X : A) return My_Index is (X'Length); --@RANGE_CHECK:FAIL
end Mod_Array;
