procedure Sub (X, Y : in out Integer) with
  Pre  => X + Y - 1 = Integer'Last,    --  @OVERFLOW_CHECK:FAIL
  Post => X = Integer'Last and Y = 1
is
begin
  null;
end Sub;
