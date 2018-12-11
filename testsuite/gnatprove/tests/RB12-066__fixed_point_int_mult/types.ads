package Types with SPARK_Mode is
   type T is delta 1.0 / 128.0 range 0.0 .. 2000.0;
   type M is mod 2 ** 8;

   function Mul_OK (X, Y : T) return M is
     (M (X * Y))
   with Pre => X <= 10.0 and Y <= 25.0;

   function Mul_KO1 (X, Y : T) return M is
     (M (X * Y)) --@RANGE_CHECK:FAIL
   with Pre => X <= 10.0 and Y <= 26.0;

   subtype M2 is M range 0 .. 100;

   function Mul_KO2 (X, Y : T) return M2 is
     (M2 (X * Y)) --@RANGE_CHECK:FAIL
   with Pre => X <= 10.0 and Y <= 25.0;

   type M3 is mod 100;

   function Mul_KO3 (X, Y : T) return M3 is
     (M3 (X * Y)) --@RANGE_CHECK:FAIL
   with Pre => X <= 10.0 and Y <= 25.0;

   type T2 is delta 128.0 range 0.0 .. 2000.0;

   function Mul_OK (X : T; Y : T2) return M is
     (M (X * Y))
   with Pre => X < 1.0 and Y <= 300.0;
end Types;
