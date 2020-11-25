procedure Lemma_Mul_By_Less_Than_One
  (Val1 : Float;
   Val2 : Float)
with
  Pre  => Val1 in 0.0 .. 1.0 and Val2 >= 0.0,
  Post => Val1 * Val2 <= Val2
is
begin
   null;
end;
