with Sub;
procedure Top (X : in out Integer) with
  SPARK_Mode
is
begin
   Sub (X);
end Top;
