with Ada.Unchecked_Conversion;
procedure Main
  with SPARK_Mode => On
is
   type My_Enum is (A, B, C, D) with Size => 3;

   for My_Enum use
     (A => 0,
      B => 1,
      C => 2,
      D => 7);

   type Mod_8 is mod 8 with Size => 3;

   function Conv is new Ada.Unchecked_Conversion (My_Enum, Mod_8);

   V : Mod_8 := Conv (D);

begin
   pragma Assert (V = 3); -- @ASSERT:FAIL
end Main;
