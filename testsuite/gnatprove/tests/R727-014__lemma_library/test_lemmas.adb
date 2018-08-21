with SPARK.Integer_Arithmetic_Lemmas;
with SPARK.Long_Integer_Arithmetic_Lemmas;
with SPARK.Float_Arithmetic_Lemmas;
with SPARK.Long_Float_Arithmetic_Lemmas;

procedure Test_Lemmas is
   X, Y, Z : Integer := 1;
   U, V, W : Long_Integer := 1;
   A, B, C : Float := 1.0;
   D, E, F : Long_Float := 1.0;

begin
   SPARK.Integer_Arithmetic_Lemmas.Lemma_Div_Is_Monotonic (X, Y, Z);
   SPARK.Long_Integer_Arithmetic_Lemmas.Lemma_Div_Is_Monotonic (U, V, W);

   SPARK.Float_Arithmetic_Lemmas.Lemma_Add_Is_Monotonic (A, B, C);
   SPARK.Long_Float_Arithmetic_Lemmas.Lemma_Add_Is_Monotonic (D, E, F);
end Test_Lemmas;
