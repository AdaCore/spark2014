procedure exchange (x, y : in out item) is
   tmp : item := x;
begin
   x := y;
   y := tmp;
end exchange;
