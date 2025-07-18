package Calendar with SPARK_Mode => On is

   type T1 is private;
   type T2 is private;
   type T3 is private;

   function Mult (X : T1; Y : T2) return T3;

private
   type T1 is delta 1.0 / 1_000.0 range 0.0 .. 1_000.0;
   type T2 is delta 1_000.0 range 0.0 .. 1_000_000_000.0;
   type T3 is delta 1.0 range 0.0 .. 1_000_000.0;

end Calendar;
