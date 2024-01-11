with Ada.Unchecked_Conversion;

procedure Unsigned is
   type S32 is range -2**31 .. 2**31-1 with Size => 32;
   type U32 is range 0 .. 2**32-1 with Size => 32;
   type B32 is range -1 .. 2**32-2 with Size => 32;

   function To_U32 is new Ada.Unchecked_Conversion (Source => S32, Target => U32);

   function To_B32 is new Ada.Unchecked_Conversion (Source => S32, Target => B32);

   procedure Test_Unsigned with Pre => True is
      U : U32;
   begin
      U := To_U32 (S32'First);
      pragma Assert (U < 0); -- @ASSERT:FAIL
   end;

   procedure Test_Biased with Pre => True is
      B : B32;
   begin
      B := To_B32 (S32'First);
      pragma Assert (B < -1); -- @ASSERT:FAIL
   end;
begin
   Test_Unsigned;
   Test_Biased;
end;
