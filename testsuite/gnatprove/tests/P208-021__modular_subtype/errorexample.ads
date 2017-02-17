pragma SPARK_Mode;

package ErrorExample is

   type Unsigned_32 is mod 2**32;
   subtype Unsigned_32_m1_0_M100_0 is Unsigned_32 range 1 .. 100;

   procedure comp
      (Calculated_Force : Unsigned_32_M1_0_M100_0);
end ErrorExample;
