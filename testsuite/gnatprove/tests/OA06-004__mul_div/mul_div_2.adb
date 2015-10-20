package body Mul_Div_2
  with SPARK_Mode => On
is

   function Mul_Div (V : LLI; M : Natural; D : Positive) return LLI
   is
      --  We first multiply V * M and then divide the result by D using 128-bit
      --  temporary values composed of two 64-bit words (high and low part).

      V_Hi : constant LLI := V / 2 ** 32;
      V_Lo : constant LLI := V rem 2 ** 32;
      --  High and low parts of V

      V_M_Hi, V_M_Lo : LLI;
      --  High and low parts of V * M (+-) D / 2

      Result_Hi, Result_Lo : LLI;
      --  High and low parts of the result

      Remainder : LLI;
      --  Remainder of the first division

   begin
      --  Multiply V * M and add/subtract D/2
      V_M_Lo := V_Lo * LLI (M) + (if V >= 0 then 1 else -1) * LLI (D / 2);
      V_M_Hi := V_Hi * LLI (M) + V_M_Lo / 2 ** 32;
      V_M_Lo := V_M_Lo rem 2 ** 32;

      --  First quotient
      Result_Hi := V_M_Hi / LLI (D);

      if Result_Hi not in -(2 ** 31) .. 2 ** 31 - 1 then

         --  The final result would overflow anyway

         raise Constraint_Error;
      end if;

      Remainder := V_M_Hi rem LLI (D);

      Result_Hi := Result_Hi * 2 ** 32;

      --  Second quotient

      Result_Lo := (V_M_Lo + Remainder * 2 ** 32) / LLI (D);

      --  Combine low and high parts of the result

      return Result_Hi + Result_Lo;

   end;

end;
