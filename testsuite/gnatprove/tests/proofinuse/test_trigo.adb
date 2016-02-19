with Ada.Text_IO; use Ada.Text_IO;
with Trigo;
with Ada.Numerics.Elementary_Functions;

procedure Test_Trigo is
   F : Float;
   Dummy : Float;
begin
   Put_Line ("test sin");
   F := -1.0;
   while F <= 1.0 loop
      Dummy := Trigo.Sin (F);
      F := Float'Succ (F);
   end loop;
   Put_Line ("test sin ok");

   Put_Line ("test cos");
   F := -1.0;
   while F <= 1.0 loop
      Dummy := Trigo.Cos (F);
      F := Float'Succ (F);
   end loop;
   Put_Line ("test cos ok");

   Put_Line ("test tan");
   F := -0.5;
   while F <= 0.5 loop
      Dummy := Trigo.Tan (F);
      F := Float'Succ (F);
   end loop;
   Put_Line ("test tan ok");

   Put_Line ("test tan = sin / cos");
   F := -0.5;
   while F <= 0.5 loop
      pragma Assert (abs (Trigo.Tan (F) - Trigo.Sin (F) / Trigo.Cos (F)) < 0.001);
      F := Float'Succ (F);
   end loop;
   Put_Line ("test tan = sin / cos ok");
end Test_Trigo;
