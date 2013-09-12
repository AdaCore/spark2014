package body Pck is pragma SPARK_Mode (On);
   function Mul_Div (V : Uint_64; M : Natural; D : Natural) return Uint_64 is

      --  Upper case letters represent one word (32-bit words in our case).
      --  If we can compute, PQ = AB / D, then we can compute ABC / D using
      --  the following method (pencil and paper algorithm):

      --  MN  := AB / D       (first quotient)
      --  R   := AB - MN * D  (remainder on one word, as R < D)
      --  OP  := RC / D       (second quotient)
      --  res := MN0 + OP

      --  We check absence of overflow in the final result by checking that
      --  M is 0, and that there is no carry when adding N0 and OP.

      V_Hi : Uint_64 := V / 2 ** 32;   -- AB
      V_Lo : Uint_64 := V rem 2 ** 32; --  C

      Result_Hi : Uint_64;
      --  High part of the result

      Result_Lo : Uint_64;
      --  Low part of the result

      Remainder : Uint_64;
      --  Remainder of the first division (denoted R above)

   begin
      --  Multiply V by M

      V_Hi := V_Hi * Uint_64 (M);
      V_Lo := V_Lo * Uint_64 (M);
      V_Hi := V_Hi + V_Lo / 2 ** 32;
      V_Lo := V_Lo rem 2 ** 32;

      --  First division

      Result_Hi := V_Hi / Uint_64 (D);

      pragma Assert (Result_Hi < Uint_64 (Natural'Last));
      --  if Result_Hi >= Uint_64 (Natural'Last) then

         --  The resulting conversion would overflow

         --  raise Constraint_Error;

      --  end if;

      Remainder := V_Hi - Result_Hi * Uint_64 (D);

      Result_Hi := Result_Hi * 2 ** 32;

      --  Second division. To improve rounding, D / 2 is added

      Result_Lo :=
        (V_Lo + Remainder * 2 ** 32 + Uint_64 (D) / 2) / Uint_64 (D);

      pragma Assert
         (Result_Lo <= Uint_64 (Natural'Last) * 2 ** 32 - Result_Hi);

      --  if Result_Lo > Uint_64 (Natural'Last) * 2 ** 32 - Result_Hi  then

         --  The resulting conversion would overflow

      --     raise Constraint_Error;
      --  end if;

      return Result_Hi + Result_Lo;
   end Mul_Div;
end Pck;
