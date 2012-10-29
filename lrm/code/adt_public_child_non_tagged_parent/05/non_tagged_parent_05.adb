package body Pairs
is   

   function Sum (Value : in Pair) return Integer
   is
   begin
        return Value.Value_One + Value.Value_Two;
   end Sum;

end Pairs;

