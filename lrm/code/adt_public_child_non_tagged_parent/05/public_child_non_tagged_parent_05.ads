--#inherit non_tagged_parent_05;

package non_tagged_parent_05.public_child_non_tagged_parent_05
is

   --  Additional operation to add to the ADT, which
   --  increments each value in the Pair.
   procedure Increment (Value: in out non_tagged_parent_05.Pair);
   --# derives Value from Value;

private

   --  Variable declared to illustrate access to private part of
   --  parent from private part of child.
   Own_Inc_Value : constant Integer := non_tagged_parent_05.Inc_Value;

end non_tagged_parent_05.public_child_non_tagged_parent_05;
