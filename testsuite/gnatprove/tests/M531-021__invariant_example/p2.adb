package body P2
  with SPARK_Mode => On
is
   subtype Upper_Range is Natural range 0 .. Root_Of_Natural_Last + 1;

   function Sqrt (N : in Natural) return Sqrt_Range
   is
      Lower   : Sqrt_Range;
      Upper   : Upper_Range;
      Halfway : Sqrt_Range;
   begin
      Lower := 0;
      Upper := Upper_Range'Last;

      loop
         -- Note Long_Long_Integer needed here to avoid overflow
         -- on first evaluation
         pragma Loop_Invariant
           (Lower * Lower <= N and
              Long_Long_Integer (Upper) * Long_Long_Integer (Upper) >
              Long_Long_Integer (N));

         exit when Upper = Lower + 1;

         Halfway := (Lower + Upper) / 2;

         if Halfway * Halfway <= N then
            Lower := Halfway;
         else
            Upper := Halfway;
         end if;
      end loop;

      return Lower;
   end Sqrt;

end P2;


