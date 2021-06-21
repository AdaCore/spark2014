procedure Swap (X, Y : in out Integer) with
  SPARK_Mode,
  Depends => (X => Y, Y => X),
  Post    => X = Y'Old and Y = X'Old
is
   Tmp : constant Integer := X;
begin
   X := Y;
   Y := Tmp;
end Swap;
