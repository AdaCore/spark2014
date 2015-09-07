with Ada.Numerics;
package Common_Units is

   type Degrees is digits 18 range 0.0 .. 360.0;
   type Radians is digits 18 range 0.0 .. 2.0 * Ada.Numerics.Pi;

   type Volts is delta 1.0 / 2.0**12 range -45_000.0 .. 45_000.0;
   type Amps  is delta 1.0 / 2.0**16 range -1_000.0 .. 1_000.0;
   type Ohms  is delta 0.125         range  0.0 .. 1.0E8;

   type Light_Years is digits 12 range 0.0 .. 20.0E9;

   subtype Percent is Integer range 0 .. 100;
end Common_Units;