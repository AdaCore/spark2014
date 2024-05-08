procedure B with SPARK_Mode is
  X : Integer := 0;

  procedure Incr (X : in out Integer) with Pre => X < Integer'Last;
  procedure Incr (X : in out Integer) is begin X := X + 1; end Incr;
begin
  Incr (X);
end B;
