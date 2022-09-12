with SPARK.Lemmas.Integer_Arithmetic; use SPARK.Lemmas.Integer_Arithmetic;

procedure Signed with
  SPARK_Mode
is
   type U is range 0 .. 2 ** 63 - 1;
begin
   for I in 0 .. 62 loop
      Lemma_Exp_Is_Monotonic_2 (Val => 2, Exp1 => I, Exp2 => 62);
      pragma Assert (2 ** I <= 2 ** 62);
      pragma Loop_Invariant (for all K in 0 .. I => 2 ** K in U'Range);
   end loop;

   pragma Assert (for all I in 0 .. 62 => 2 ** I in U'Range);
end Signed;
