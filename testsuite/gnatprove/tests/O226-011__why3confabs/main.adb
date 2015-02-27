procedure Main is
   X, Y : Integer;

   function F return Integer is (1)
      with Post => (F'Result > 0);
begin
   X := F;
   Y := X * X;
end Main;
