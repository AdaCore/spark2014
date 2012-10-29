--  TBD: confirm that no inherits clause and check
--  whether anything needed in its place.

package Pairs.Additional
is

   --  Additional operation to add to the ADT, which
   --  increments each value in the Pair.
   procedure Increment (Value: in out Pairs.Pair);
   with
      Depends => (Value => Value);

private

   --  Variable declared to illustrate access to private part of
   --  parent from private part of child.
   Own_Inc_Value : constant Integer := Pairs.Inc_Value;

end Pairs.Additional;