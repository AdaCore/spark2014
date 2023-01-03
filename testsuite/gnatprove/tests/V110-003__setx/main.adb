procedure Main is
   X : Integer;
   procedure SetX (N : Integer)
     with Post => X > N is -- @COUNTEREXAMPLE
   begin
      X := N+1;
   end SetX;
begin
  X := 0;
  SetX(2);
  pragma Assert ( X = 3 ); -- @COUNTEREXAMPLE
end Main;
