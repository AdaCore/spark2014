procedure Main is
  function F return Integer is (0) with Post => True;
  X, Y, Z : Integer := F;
begin
  X := X + 1;
  Y := Y + 1;
  Z := Z + 1;
end Main;
