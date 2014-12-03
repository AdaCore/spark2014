procedure Swap_Bad_Post (X, Y : in out Integer) with
  SPARK_Mode,
  Post => X = Y'Old and Y = X'Old
is
begin
   X := Y;
   Y := X;
end Swap_Bad_Post;
