package Alias is

   type T is private;
   --  Descendant of a private type whose full type is a by-copy type (a type
   --  is descendant of itself).
   --  See Ada RM 6.2(3).

   procedure Test;
   --  This procedure is alias-free because T is a by-copy type.
   --  In the past, gnatprove chose to be conservative and assume the worst-case
   --  (by-reference) for T to preserve the abstraction of the private part.
   --  However this interpretation is not quite consistent with the Ada RM.

private

   type T is new Integer;

end;
