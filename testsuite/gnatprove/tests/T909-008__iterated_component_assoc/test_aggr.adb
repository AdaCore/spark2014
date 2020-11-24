procedure Test_Aggr with SPARK_Mode is
   type My_Arr is array (Positive range <>) of Integer;

   A : My_Arr :=
     (1     => 0,
      2 | 5 => 1,
      for I in 3 .. 4 | 6 .. 10 => I + 15, --@OVERFLOW_CHECK:PASS
      11 => 33);

begin
   null;
end Test_Aggr;
