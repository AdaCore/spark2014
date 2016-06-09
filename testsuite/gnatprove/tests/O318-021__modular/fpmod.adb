procedure Fpmod with
  SPARK_Mode
is
   type F is delta 0.01 range -1.0 .. 0.99;
   type M is mod 2 ** 8;

   X : F;
   Y : M;
begin
   X := 0.5;
   Y := M(X);
   X := -0.1;
   Y := M(X);
   X := -0.5;
   Y := M(X);  --  @RANGE_CHECK:FAIL
end Fpmod;
