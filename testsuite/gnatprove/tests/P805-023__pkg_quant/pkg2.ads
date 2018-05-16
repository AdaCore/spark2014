package Pkg2 with SPARK_Mode => On is

   function F (X : Integer) return Integer
      with SPARK_Mode => Off;

private
   pragma SPARK_Mode (Off);

   X : constant Boolean := (for all X in Integer => F (X) = X);
end Pkg2;
