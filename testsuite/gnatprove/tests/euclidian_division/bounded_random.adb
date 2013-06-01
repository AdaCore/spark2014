with Linear_Div;
with Ada.Numerics.Discrete_Random;

--  Return a random natural number inferior to Max
--
--  The spec of this procedure is in SPARK.
--  The body of this procedure is not in SPARK though,
--  as Random_Integer.Random is not a pure function.

procedure Bounded_Random
  (Max    : Integer;
   Result : out Integer)
with Pre  => Max >= 0,
     Post => Result >= 0 and Result < Max
is
   package Random_Integer is new Ada.Numerics.Discrete_Random (Integer);

   Quotient : Integer;
   Gen      : Random_Integer.Generator;
begin
   Linear_Div (Random_Integer.Random (Gen), Max, Quotient, Result);
end Bounded_Random;
