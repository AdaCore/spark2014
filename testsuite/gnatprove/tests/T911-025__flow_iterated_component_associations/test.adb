procedure Test with SPARK_Mode is
   type My_Int is range 1 .. 20;
   type My_Arr is array (My_Int range <>) of My_Int;

   A : My_Arr (1 .. 20);

begin
   A := (for J in 1 .. 5 => J, for J in My_Int range 6 .. 10 => J, for J in others => J);
   A := (for J in My_Int => J);
   A := (for J in 6 | 7 | My_Int range 15 .. 20 => J, others => 1);
end Test;
