package body Money
  with SPARK_Mode
is

   function "+" (A, B : Amount) return Amount is
     (Amount'(A.Currency, A.Raw + B.Raw));

   function "-" (A, B : Amount) return Amount is
     (Amount'(A.Currency, A.Raw - B.Raw));

end Money;
