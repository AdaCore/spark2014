package Alias is

   type T is private;
   --  Descendant of a private type whose full type is a by-copy type (a type
   --  is descendant of itself).

   procedure Test;
   --  This procedure is alias-free because T is a by-copy type; however,
   --  gnatprove chooses to be conservative and assumes the worst-case
   --  (by-reference) for T to preserve the abstraction of the private part.

private

   type T is new Integer;

end;
