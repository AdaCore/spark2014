package Conversion_Fixed is

   type T is delta 2.0/5.0 range -10.0 .. 10.0 with Small => 2.0/5.0;
   type T2 is delta 1.0/25.0 range -10.0 .. 10.0 with Small => 1.0/25.0;
   type T3 is delta 1.0 range -10.0 .. 10.0 with Small => 1.0;
   type T4 is delta 2.0 range -10.0 .. 10.0 with Small => 2.0;

   procedure Test (X : T; X2 : T2; X3 : T3; X4 : T4);

end Conversion_Fixed;
