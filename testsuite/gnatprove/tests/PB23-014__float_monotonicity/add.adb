procedure Add (X1, X2 : in out Float;
               Y      : in Float)
  with SPARK_Mode,
       Pre => X1 in -2_000_000.0 .. 2_000_000.0
               and then X2 in -2_000_000.0 .. 2_000_000.0
               and then X1 <= X2
               and then Y in -1.0 .. 1.0,
       Post => X1 <= X2
is
begin
   X1 := X1 + Y;
   X2 := X2 + Y;
end Add;
