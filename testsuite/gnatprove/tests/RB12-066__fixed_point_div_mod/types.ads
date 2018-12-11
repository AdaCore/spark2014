package Types with SPARK_Mode is
   type T is delta 1.0 / 128.0 range 0.0 .. 20.0;
   type M is mod 2 ** 8;

   function Div_OK (X, Y : T) return M is
     (M (X / Y))
   with Pre => Y /= 0.0 and then X <= 1.0;

   function Div_KO1 (X, Y : T) return M is
     (M (X / Y)) --@RANGE_CHECK:FAIL
   with Pre => Y /= 0.0;

   subtype M2 is M range 0 .. 100;

   function Div_KO2 (X, Y : T) return M2 is
     (M2 (X / Y)) --@RANGE_CHECK:FAIL
   with Pre => Y /= 0.0 and then X <= 1.0;

   type M3 is mod 100;

   function Div_KO3 (X, Y : T) return M3 is
     (M3 (X / Y)) --@RANGE_CHECK:FAIL
   with Pre => Y /= 0.0 and then X <= 1.0;
end Types;
