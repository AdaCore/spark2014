package Greatest_Common_Divisor
   with SPARK_Mode
is
   function Gcd (A, B : Natural) return Natural
     with Ghost, Import, Global => Null;

   procedure G_C_D (M, N : in Natural; G : out Natural)
     with
     Depends => (G => (M, N)),
     Post => G = Gcd (M, N);

end Greatest_Common_Divisor;
