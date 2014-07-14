with Test; use Test;

procedure Main (A, B : in out Record_T)
  with Post => A = B
is
begin
   A.X := (A.X + B.X) / 2;
   B.X := A.X;
end Main;
