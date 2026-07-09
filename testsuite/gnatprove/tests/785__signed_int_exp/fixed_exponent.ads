package Fixed_Exponent
  with SPARK_Mode
is

   --  Exponentiation by a literal exponent. These checks exercise how
   --  provers handle "**" once the exponent is a compile-time constant,
   --  from trivial cases to nonlinear overflow reasoning.

   subtype Small is Integer range -1_000 .. 1_000;

   function Square (X : Small) return Integer
   with Post => Square'Result = X * X;

   function Cube (X : Small) return Integer
   with Post => Cube'Result = X * X * X;

   subtype Bounded_For_Fourth is Integer range -215 .. 215;

   function Fourth_Power (X : Bounded_For_Fourth) return Integer
   with Post => Fourth_Power'Result = X * X * X * X;

   subtype Bounded_For_Fifth is Integer range -70 .. 70;

   function Fifth_Power (X : Bounded_For_Fifth) return Integer;

end Fixed_Exponent;
