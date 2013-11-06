procedure Example1
is
   X : Integer;
begin
   X := 475799;
   pragma Assert (for some N in Natural range 2 .. X - 1 => (X mod N = 0));
end Example1;
