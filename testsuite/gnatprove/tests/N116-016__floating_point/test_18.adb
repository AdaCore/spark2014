procedure Test_18 (X : Float;
                   Z : out Float)
  with Pre  => (X in 0.0 .. 10.0) and (X in 5.0 .. 20.0),
       Post => Z >= X  --  ok
is
begin
   Z := (X * 2.0) - 5.0;
end Test_18;
