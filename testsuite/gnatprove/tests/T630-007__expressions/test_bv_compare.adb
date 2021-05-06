procedure Test_BV_Compare with SPARK_Mode is
   type T is mod 2**8;

   function Rand (X : T) return T with Import;
   function Id (X : Boolean) return Boolean is (X);

   X : T := Rand (1);
   Y : T := Rand (2);
begin
   pragma Assert (if Id (X /= Y) then Id ((X < Y) = (Y >= X)));
   pragma Assert (Id (X = Y) or else Id ((X <= Y) = (Y > X)));
end Test_BV_Compare;
