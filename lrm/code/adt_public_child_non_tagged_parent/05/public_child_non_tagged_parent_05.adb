package body non_tagged_parent_05.public_child_non_tagged_parent_05
is   

   procedure Increment (Value: in out non_tagged_parent_05.Pair) is
   begin
      -- Access to private part of parent from body of public child.
      Value.Value_One := Value.Value_One + Own_Inc_Value;
      Value.Value_Two := Value.Value_Two + Own_Inc_Value;
   end Increment;

end non_tagged_parent_05.public_child_non_tagged_parent_05;
