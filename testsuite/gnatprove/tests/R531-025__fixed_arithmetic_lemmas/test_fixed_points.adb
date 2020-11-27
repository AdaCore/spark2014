pragma SPARK_Mode;
with SPARK.Fixed_Point_Arithmetic_Lemmas;

package body Test_Fixed_Points is

   package Lemmas is new SPARK.Fixed_Point_Arithmetic_Lemmas (Fix);

   procedure Test_Div_Is_Monotonic
     (Val1  : Fix;
      Val2  : Fix;
      Denom : Positive)
   is
   begin
      Lemmas.GNAT_Lemma_Div_Is_Monotonic (Val1, Val2, Denom);
   end Test_Div_Is_Monotonic;

   procedure Test_Div_Right_Is_Monotonic
     (Num    : Fix;
      Denom1 : Positive;
      Denom2 : Positive)
   is
   begin
      Lemmas.GNAT_Lemma_Div_Right_Is_Monotonic (Num, Denom1, Denom2);
   end Test_Div_Right_Is_Monotonic;

   procedure Test_Mult_Then_Div_Is_Ident
     (Val1 : Fix;
      Val2 : Positive)
   is
   begin
      Lemmas.GNAT_Lemma_Mult_Then_Div_Is_Ident (Val1, Val2);
   end Test_Mult_Then_Div_Is_Ident;

end Test_Fixed_Points;
