with Ada.Numerics; use Ada.Numerics;

package Pack is
   pragma SPARK_Mode (On);
   Two_Pi  : constant := 2 * Pi;

   Four_Pi : constant Float := 2.0 * Two_Pi;

   Four    : constant := 4;

   Eight   : constant Integer := 2 * Four;

end Pack;
