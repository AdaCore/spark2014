procedure Swap_Bad (X, Y : in out Integer) with
  SPARK_Mode
is
begin
   X := Y;
   Y := X;
end Swap_Bad;
