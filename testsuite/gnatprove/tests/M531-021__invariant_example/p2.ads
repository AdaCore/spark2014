package P2
  with SPARK_Mode => On
is
   pragma Assert (Natural'Last = 16#7FFF_FFFF#);

   Root_Of_Natural_Last : constant := 16#B504#;

   subtype Sqrt_Range is Natural range 0 .. Root_Of_Natural_Last;

   function Sqrt (N : in Natural) return Sqrt_Range
     with Post => (Sqrt'Result * Sqrt'Result)           <= N and
                  (Sqrt'Result + 1) * (Sqrt'Result + 1) >  N;

end P2;


