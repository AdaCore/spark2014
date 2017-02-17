procedure P (A, B : Integer) is
   pragma Precondition (A in 1 .. 20 and then B in 1 .. 20);
   X : array (1..20) of Integer := (others => -123);
begin
   X (A) := 1;
   X (B) := 2;
   pragma Assert (if A /= B then X (A) = 1);
end;
