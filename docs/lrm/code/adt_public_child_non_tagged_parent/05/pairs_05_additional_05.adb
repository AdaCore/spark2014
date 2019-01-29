package body Pairs_05.Additional_05
is

   procedure Increment (Value: in out Pairs_05.Pair) is
   begin
      -- Access to private part of parent from body of public child.
      Value.Value_One := Value.Value_One + Own_Inc_Value;
      Value.Value_Two := Value.Value_Two + Own_Inc_Value;
   end Increment;

end Pairs_05.Additional_05;
