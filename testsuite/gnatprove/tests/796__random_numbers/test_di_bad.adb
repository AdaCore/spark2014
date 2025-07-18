with Ada.Numerics.Discrete_Random;

procedure Test_Di_Bad with SPARK_Mode => On is

   package Random_Integer is new Ada.Numerics.Discrete_Random (Integer);
   use Random_Integer;

   G : Generator;

   -- Call to Random (a function with side-effect) within a declare block is not
   -- supported by SPARK. They must be initialized later.
   X, Y : Integer;

begin
   X := Random (G);
   Y := Random (G);

   pragma Assert (X = Y); -- @ASSERT:FAIL

end Test_Di_Bad;
