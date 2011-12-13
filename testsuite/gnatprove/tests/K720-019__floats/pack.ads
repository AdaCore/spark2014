package Pack is

   type Coefficient is digits 10 range -1.0 .. 1.0;

   type Real is digits 8;
   type Mass is digits 7 range 0.0 .. 1.0E35;

   subtype Probability is Real range 0.0 .. 1.0;

   function Add (R1, R2 : Float) return Float
     with Pre => (R1 < 1.0
                  and then R2 < 1.0
                  and then R1 > -1.0
                  and then R2 > -1.0),
          Post => (Add'Result = (R1 + R2));

   function Associativity_Test return Boolean
     with Post => (Associativity_Test'Result = True);

end Pack;
