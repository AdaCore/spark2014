--#inherit Pairs_05;

package Pairs_05.Additional_05
is

   --  Additional operation to add to the ADT, which
   --  increments each value in the Pair.
   procedure Increment (Value: in out Pairs_05.Pair);
   --# derives Value from Value;

private

   --  Variable declared to illustrate access to private part of
   --  parent from private part of child.
   Own_Inc_Value : constant Integer := Pairs_05.Inc_Value;

end Pairs_05.Additional_05;
