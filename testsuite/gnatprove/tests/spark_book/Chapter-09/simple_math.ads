pragma SPARK_Mode;

package Simple_Math is

   subtype Square_Root_Domain is Integer range 0 .. 1_000_000;
   subtype Square_Root_Range  is Square_Root_Domain range 0 .. 1_000;

   function Square_Root(N : Square_Root_Domain) return Square_Root_Range;

end Simple_Math;
