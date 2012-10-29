--#inherit Pairs;

package Pairs.Additional
is

   --  Additional operation to add to the ADT, which
   --  increments each value in the Pair.
   procedure Increment (Value: in out Pairs.Pair);
   --# derives Value from Value;

private

   --  Variable declared to illustrate access to private part of
   --  parent from private part of child.
   Own_Inc_Value : constant Integer := Pairs.Inc_Value;

end Pairs.Additional;
