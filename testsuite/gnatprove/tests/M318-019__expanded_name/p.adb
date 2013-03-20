pragma Ada_2012;
procedure P (A, B : Integer)
  with Pre => A <= B
is
   type T is array (A .. B) of Integer;
   X : P.T := (others => P.T'First);
begin
   pragma Assert (for all J in A .. B => X(J) = A);
end P;
