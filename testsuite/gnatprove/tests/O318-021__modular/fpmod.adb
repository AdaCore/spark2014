procedure Fpmod with
  SPARK_Mode
is
   type F is delta 0.01 range 0.0 .. 1.0;
   type M is mod 2 ** 8;

   X : F := 0.5;
   Y : M;
begin
   Y := M(X);
end Fpmod;
