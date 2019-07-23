package body Pairs_05
is

   function Sum (Value : in Pair) return Integer
   is
   begin
        return Value.Value_One + Value.Value_Two;
   end Sum;

end Pairs_05;

