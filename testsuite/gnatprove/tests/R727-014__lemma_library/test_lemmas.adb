with SPARK.Lemmas.Integer_Arithmetic;
with SPARK.Lemmas.Long_Integer_Arithmetic;
with SPARK.Lemmas.Float_Arithmetic;
with SPARK.Lemmas.Long_Float_Arithmetic;

procedure Test_Lemmas is
   X, Y, Z : Integer := 1;
   U, V, W : Long_Integer := 1;
   A, B, C : Float := 1.0;
   D, E, F : Long_Float := 1.0;

begin
   SPARK.Lemmas.Integer_Arithmetic.Lemma_Div_Is_Monotonic (X, Y, Z);
   SPARK.Lemmas.Long_Integer_Arithmetic.Lemma_Div_Is_Monotonic (U, V, W);

   SPARK.Lemmas.Float_Arithmetic.Lemma_Add_Is_Monotonic (A, B, C);
   SPARK.Lemmas.Long_Float_Arithmetic.Lemma_Add_Is_Monotonic (D, E, F);
end Test_Lemmas;
