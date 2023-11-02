procedure A (X : in out Integer) with SPARK_Mode, Pre => X < Integer'Last is
begin
  X := X + 1;
  X := X + 1;
end A;
