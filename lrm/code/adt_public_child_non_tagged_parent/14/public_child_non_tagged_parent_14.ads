--  TBD: confirm that no inherits clause and check
--  whether anything needed in its place.

package non_tagged_parent_14.public_child_non_tagged_parent_14
is

   --  Additional operation to add to the ADT, which
   --  increments each value in the Pair.
   procedure Increment (Value: in out non_tagged_parent_14.Pair);
   with
      Depends => Value => Value;

private

   --  Variable declared to illustrate access to private part of
   --  parent from private part of child.
   Own_Inc_Value : constant Integer := non_tagged_parent_14.Inc_Value;

end non_tagged_parent_14.public_child_non_tagged_parent_14;
