procedure Sub (X, Y : in out Integer) with
  Pre  => X + Y - 1 = Integer'Last,
  Post => X = Integer'Last and Y = 1
is
begin
  null;
end Sub;
