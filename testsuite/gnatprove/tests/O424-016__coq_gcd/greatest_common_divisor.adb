package body Greatest_Common_Divisor
   with SPARK_Mode
is
   procedure G_C_D (M, N : in Natural; G : out Natural)
   is
      C, D, R : Natural;
   begin
      C := M; D := N;
      loop
         pragma Loop_Invariant (Gcd (C, D) = Gcd (M, N));

         -- FIXME workaround for [N410-033]
         exit when D = 0;

         R := C mod D;
         C := D; D := R;
      end loop;
      G := C;
   end G_C_D;

end Greatest_Common_Divisor;
