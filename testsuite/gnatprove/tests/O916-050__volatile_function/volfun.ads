package Volfun
  with SPARK_Mode
is
   function F return Integer is (0) with Volatile_Function;
   function G return Integer is (F + 1) with Volatile_Function;
   function H return Integer;
end Volfun;
