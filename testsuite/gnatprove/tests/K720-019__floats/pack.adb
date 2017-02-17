package body Pack is

   function Add (R1, R2 : Float) return Float is
   begin
      return R1 + R2;
   end Add;

   function Associativity_Test return Boolean is
   begin
      return Add (Add (0.1, 0.2), 0.3) = Add (0.1, Add (0.2, 0.3));
   end Associativity_Test;

end Pack;
