with Ada.Numerics.Discrete_Random;
with Ada.Text_IO; use Ada.Text_IO;

procedure Test_Di_Good with SPARK_Mode => On is

   package Random_Integer is new Ada.Numerics.Discrete_Random (Integer);
   use Random_Integer;

   G : Generator;

   -- Call to Random (a function with side-effect) within a declare block is
   -- not supported in SPARK. They must be initialized later.
   X, Y : Integer;

begin

   Put_Line ("-- Basic facilities --");

   X := Random (G);
   Y := Random (G, 100, 300);
   Put_Line ("X = " & Integer'Image (X) & ", Y = " & Integer'Image (Y));

   Put_Line ("Resetting generator with default initial condition");
   Reset (G);

   X := Random (G);
   Put_Line ("X = " & Integer'Image (X));

   Put_Line ("Resetting generator with fixed initial condition");
   Reset (G, 42);

   for I in 1 .. 3 loop
      X := Random (G);
      Put_Line ("X = " & Integer'Image (X));
   end loop;

   Put_Line ("Resetting generator again with the same initial condition");
   Reset (G, 42);

   for I in 1 .. 3 loop
      X := Random (G);
      Put_Line ("X = " & Integer'Image (X));
   end loop;

   Put_Line ("-- Advanced facilities --");

   declare
      S1, S2 : State;
   begin
      Save (G, S1);
      Put_Line ("Saved state to S1");
      Save (G, S2);
      Put_Line ("Saved state to S2");

      X := Random (G);
      Put_Line ("X = " & Integer'Image (X));

      Put_Line ("Resetting back to state S1");
      Reset (G, S1);
      X := Random (G);
      Put_Line ("X = " & Integer'Image (X));

      Put_Line ("Resetting back to state S2");
      Reset (G, Value (Image (S2)));
      X := Random (G);
      Put_Line ("X = " & Integer'Image (X));
   end;

end Test_Di_Good;
