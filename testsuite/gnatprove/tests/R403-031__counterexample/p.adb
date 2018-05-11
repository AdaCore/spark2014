--  This proof was originally done by Claude Marché in Why3 and can be found
--  in the repository of Why3: examples/in_progres/isqrt_von_neumann

with Interfaces; use Interfaces;

package body P
  with SPARK_Mode => On
is

   -- Auxiliary bitvectors functions for 16 bits
   function Pow2 (X : U16) return U16 is
      (Shift_Left (1, Integer(X)));

   function Sqr (X : U16) return U16 is
      (X * X);

   function Sqrt_Von_Neumann_Aux16
     (X : in U16)
      return U16
   is
      Num, Bits, Res, B : U16;

     --  Ghost entities:

      M, Bits_G, Res_G : U16 with Ghost;

   begin
      Num := X;
      pragma Assert (Num <= 2 ** 16 - 1);
      Bits  := 16#4000#;
      Res  := 0;

      M := 8;
      Bits_G := 8 * 16;
      Res_G := 0;

      while (Bits /= 0) loop
         M := M - 1;
         pragma Assert (Res = Res_G * (pow2 (M + 1)));
         pragma Assert (Bits_G = Pow2(M));
         B := Res or Bits;
         pragma Assert (B = Res + Bits);
         pragma Assert (B = ((2 * Res_G) + Bits_G) * Pow2(M));
         Res := Shift_Right (Res, 1);

         if (Num >= B) then
            Num := Num - B;
            Res  := Res or Bits;

            Res_G := Res_G + Bits_G;
         end if;

         Bits := Bits / 4;
         Bits_G := Shift_Right (Bits_G, 1);
      end loop;

      return Res;
   end Sqrt_Von_Neumann_Aux16;


end P;
