function Absolute_Value (X : Integer) return Integer
with
--  Uncomment the following line to prove
--    Pre  => X /= Integer'First,
    Post => Absolute_Value'Result = abs (X)
is
begin
   if X > 0 then
      return X;
   else
      return -X; -- @FAIL @COUNTEREXAMPLES
   end if;
end Absolute_Value;
