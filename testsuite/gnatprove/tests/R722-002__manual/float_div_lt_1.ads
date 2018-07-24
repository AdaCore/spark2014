package Float_Div_Lt_1
  with SPARK_Mode
is

   type Fixed is delta 2.0 ** (-30) range Float (Integer'First) .. Float (Integer'Last)
     with Size => 64;

   procedure Div_Lt_1 (Dividend : Integer;
                       Divisor  : Integer;
                       Quotient : Fixed)
     with
       Ghost,
       Global => null,
       Pre => (Divisor > 0 and Dividend < Divisor) and then
               Quotient = Fixed (Dividend) / Fixed (Divisor),
     Post => Quotient < 1.0;

end Float_Div_Lt_1;
