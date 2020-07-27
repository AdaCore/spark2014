procedure inc (x : in out integer) with SPARK_Mode,
  Post => X = X'Old + 1
is
begin
   x := @ + 1;
end;
