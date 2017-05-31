
-- Counterexamples from Z3
package body Float_Example
is
   type Float_7 is digits 7;

   function Minus_I (A, B: Float_7) return Float_7
     with Post => Minus_I'Result = A + B --  @COUNTEREXAMPLE
     -- Should be '-' instead of '+'
   is
   begin
      return A - B;  --  @COUNTEREXAMPLE
   end Minus_I;

   function Bounded_Add (A, B : Float_7) return Float_7
     with Pre => A < 4.0 and then B < 4.0,
     Post => Bounded_Add'Result < 7.0 --  @COUNTEREXAMPLE
     -- Should be 8.0 instead of 7.0
   is
   begin
      return A + B;  --  @COUNTEREXAMPLE
   end Bounded_Add;

end Float_Example;
