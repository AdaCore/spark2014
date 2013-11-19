package body Pairs_14.Additional_14
  with SPARK_Mode
is
   procedure Increment (Value: in out Pairs_14.Pair) is
   begin
      -- Access to private part of parent from body of public child.
      Value.Value_One := Value.Value_One + Own_Inc_Value;
      Value.Value_Two := Value.Value_Two + Own_Inc_Value;
   end Increment;
end Pairs_14.Additional_14;
