procedure Diff (X, Y : in Natural; Z : out Natural) with
  SPARK_Mode,
  Depends => (Z => (X, Y))
is
begin
   Z := X - Y;
end Diff;
