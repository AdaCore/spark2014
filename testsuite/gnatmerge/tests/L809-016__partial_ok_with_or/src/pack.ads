--
--  Copyright (C) 2011-2013, AdaCore
--

--  pragma Ada_12;

package Pack is
   --

   function P1 (X : Integer) return Integer
   with Test_Case => (Name => "test case 1",
                      Mode => Nominal,
                      Requires => X < 16,
                      Ensures  => True),
        Pre  => (X <= Integer'Last - 1),
        Post => (P1'Result = X + 1);
   --
   --

   function P2 (X : Integer) return Integer
   with Test_Case => (Name => "test case 2",
                      Mode => Robustness,
                      Requires => X < 16,
                      Ensures  => P2'Result < 4),
        Pre  => (X <= Integer'Last - 2),
        Post => (P2'Result = X + 1);
   --
   --

   function P3 (X : Integer) return Integer
   with Test_Case => (Name => "test case 3",
                      Mode => Nominal,
                      Requires => X < 16,
                      Ensures  => P3'Result < 4),
        Pre  => (X <= Integer'Last - 1),
        Post => (P3'Result = X + 5);
   --
   --

   function P4 (X : Integer) return Integer
   with Test_Case => (Name => "test case 4",
                      Mode => Robustness,
                      Requires => X < 16,
                      Ensures  => P4'Result <= 4),
        Pre  => (X <= Integer'Last - 1),
        Post => (P4'Result = X + 18);
   --
   --

   procedure P5;
   --
   --
   --
   --
   --
   --
   --
   --

   procedure P6;
   --

end Pack;
