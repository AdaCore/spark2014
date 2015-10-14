package body Mul_Div_2
  with SPARK_Mode => On
is

   function Mul_Div (V : LLI; M : Natural; D : Positive) return LLI
   is
      --  The idea is to first multiply V * M and then divide the result by D
      --  using 128-bit temporary values composed of two 64-bit words (high and
      --  low part).

      V_Hi : LLI := V / 2 ** 32;
      V_Lo : LLI := V rem 2 ** 32;
      --  High and low parts of V

      Result_Hi : LLI;
      --  High part of the result

      Result_Lo : LLI;
      --  Low part of the result

      Remainder : LLI;
      --  Remainder of the first division

   begin
      --  Multiply V by M

      V_Hi := V_Hi * LLI (M);
      V_Lo := V_Lo * LLI (M);
      V_Hi := V_Hi + V_Lo / 2 ** 32;
      V_Lo := V_Lo rem 2 ** 32;

      --  First quotient
      Result_Hi := V_Hi / LLI (D);

      if Result_Hi not in -(2 ** 31) .. 2 ** 31 - 1 then

         --  The final result would overflow anyway

         raise Constraint_Error;
      end if;

      Remainder := V_Hi rem LLI (D);

      Result_Hi := Result_Hi * 2 ** 32;

      --  Second quotient. To implement rounding required by RM D.8 (24/2),
      --  D / 2 is added.

      Result_Lo :=
        (V_Lo + Remainder * 2 ** 32 +
           (if V >= 0 then 1 else -1) * LLI (D / 2)) / LLI (D);

      if (if V >= 0
          then Result_Lo > LLI'Last  - Result_Hi
          else Result_Lo < LLI'First - Result_Hi)
      then

         --  The final addition of the result (just below) would overflow

         raise Constraint_Error;
      end if;

      return Result_Hi + Result_Lo;
   end;

end;
