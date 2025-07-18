with Ada.Numerics.Float_Random; use Ada.Numerics.Float_Random;

procedure Test_Fl_Bad with SPARK_Mode => On is

   G : Generator;

   -- Call to Random (a function with side-effect) within a declare block is not
   -- supported by SPARK. They must be initialized later.
   X, Y : Float;

begin
   X := Random (G);
   Y := Random (G);

   pragma Assert (X = Y); -- @ASSERT:FAIL

end Test_Fl_Bad;
