with Lemmas;
procedure Example2
is
   X : Integer;
begin
   X := 475799;
   pragma Assume (Lemmas.Factors_Of (X));
   pragma Assert (for some N in Natural range 2 .. X - 1 => (X mod N = 0));
end Example2;
