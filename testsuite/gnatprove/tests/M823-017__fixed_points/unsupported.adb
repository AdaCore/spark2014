procedure Unsupported is
   type T1 is delta 0.2 range -1.0 .. 1.0;
   for T1'Small use 0.2;

   type T2 is delta 1.0 range -100.0 .. 100.0;
   for T2'Small use 1.0;

   type T3 is delta 10.0 digits 10 range -100.0 .. 100.0;

   type T4 is delta 0.5 range -100.0 .. 100.0;
   type T5 is delta 0.25 range -100.0 .. 100.0;
   type T6 is delta 0.1 digits 5 range -100.0 .. 100.0;

   X4 : T4 := 0.0;
   X5 : T5 := 0.0;
   X6 : T6 := 0.0;
   X7 : Integer := 0;
begin
   X6 := X4 * X4;
   X6 := X4 * X5;
   X6 := X4 * 2.0;
   X6 := 2.0 * X4;
   X6 := T6(X4);
   X6 := T6(X5);
   X7 := Integer (X6 / X5);
end Unsupported;
