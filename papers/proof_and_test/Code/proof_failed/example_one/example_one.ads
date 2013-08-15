package Example_One is
   function Exponentiation (Var : Integer ; N :  Natural) return Integer;
   pragma Precondition  (N <= 5 and -5 <= Var and Var <= 5);
   pragma Postcondition (Exponentiation'Result = Var ** N);
   --  Returns the Nth power of Var with N <= 5 and -5 <= Var <= 5.
   --  -3125 .. 3125
end Example_One;
