procedure Proveline (X, Y : out Integer) with
  SPARK_Mode,
  Post => X > 0
      and Y > 0
is
begin
   X := 10;
   Y := 0;
end Proveline;
