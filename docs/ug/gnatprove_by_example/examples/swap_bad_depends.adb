procedure Swap_Bad_Depends (X, Y : in out Integer) with
  SPARK_Mode,
  Depends => (X => Y, Y => X)
is
begin
   X := Y;
   Y := X;
end Swap_Bad_Depends;
