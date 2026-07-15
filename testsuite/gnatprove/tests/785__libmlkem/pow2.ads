--  Reproducer distilled from the ML-KEM number-theoretic transform (the NTT
--  and NTT_Inv procedures of the LibMLKEM project).  Each NTT stage splits the
--  256-coefficient polynomial into Count = 2**I groups of stride
--  Len = 2**(7 - I), so the group count and the stride always multiply to the
--  full transform width 128 = 2**7, and the butterfly start index
--  J * 2 * Len stays within 0 .. 252.
--
--  Discharging these facts requires the prover to reason that
--  2**a * 2**b = 2**(a + b) with symbolic exponents.  Before dedicated
--  support for powers of two, provers could not do this and left the checks
--  unproved; this test guards against a regression of that support.  The
--  provers are restricted to the ones used by LibMLKEM (z3, cvc5, altergo):
--  colibri is deliberately excluded because it discharges these nonlinear
--  goals on its own and would mask a regression.

package Pow2
  with SPARK_Mode
is

   subtype Bit_Index is Natural range 0 .. 6;

   --  Count = 2**I groups of stride Len = 2**(7 - I) cover the whole width.
   procedure Stride_Product (I : Bit_Index);

   --  Same relation expressed on a local stride variable.
   procedure Width_From_Stride (I : Bit_Index);

   --  The butterfly start index J * 2 * Len never runs past 252.
   procedure Inner_Start_Bound (I : Bit_Index; J : Natural)
   with Pre => J < 2 ** I;

end Pow2;
