package prover_crash with
   SPARK_Mode => On
is

   type Myint is range 0 .. 2**32 - 1;
   for Myint'Size use 32;

   type Myfloat is digits 6;
   for Myfloat'Size use 32;

   function Crash (X, Y : Myint) return Boolean;
end prover_crash;
