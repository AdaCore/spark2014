package Pack is

   type Modular is mod 256;

   function Next (M : Modular) return Modular
     with Post => (Next'Result = M + 1);

   function Next1 (M : Modular) return Modular
     with Pre  => (M = 1),
          Post => (Next1'Result = 2);

   function Next255 (M : Modular) return Modular
     with Pre  => (M = 255),
          Post => (Next255'Result = 0);

   function Minus (A, B : Modular) return Modular
     with Pre  => (A /= B),
          Post => (Minus'Result /= 0);

   function Subst (A, B : Modular) return Modular is (A - B);
   function Test_Div (A, B : Modular) return Modular
     with Pre  => (A /= B);

end Pack;
