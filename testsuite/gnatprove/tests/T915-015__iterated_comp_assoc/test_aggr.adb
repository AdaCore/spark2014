procedure Test_Aggr with SPARK_Mode is
   type My_Int is range 1 .. 20;
   type My_Arr is array (My_Int range <>) of My_Int;

   C : My_Int := 3;
   A : My_Arr (1 .. 5);

begin
   A := (for J in others => J + C);
end Test_Aggr;
