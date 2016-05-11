with Sub;

procedure Check is
   X : Integer := Integer'Last;
   Y : Integer := 1;
begin
   Sub (X, Y);
   pragma Assert (X + Y - 1 = Integer'Last);  --  @OVERFLOW_CHECK:FAIL
end Check;
