with P; use P;

procedure Q is
   X : P.Good := 42;
begin
   pragma Assert (X = 42);
end Q;
