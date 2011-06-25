package body Money is

   function "+" (A, B : Amount) return Amount is
     (Amount'(A.Currency, A.Value + B.Value));

   function "-" (A, B : Amount) return Amount is
     (Amount'(A.Currency, A.Value - B.Value));

end Money;
