pragma Warnings (Off);

with P; use P;

procedure OK_Call with
  SPARK_Mode,
  Always_Terminates => True
is
   Y0, Y1, Y2, Y3, Y4, Y5, Y6, Y7, Y8, Y9, Y10, Y11 : Integer := 42;
begin
   Y1 := F1 (Y0);
   pragma Assert (Y0 = 42); -- @ASSERT:FAIL

   Y0 := 42;
   Y2 := F2 (Y0);
   pragma Assert (Y0 = 42); -- @ASSERT:FAIL

   G := 42;
   Y3 := F3 (1);
   pragma Assert (G = 42); -- @ASSERT:FAIL

   G := 42;
   Y4 := F4 (1);
   pragma Assert (G = 42); -- @ASSERT:FAIL

   Y5 := F5 (1); -- @RAISE:FAIL
   Y6 := F6 (1); -- @RAISE:NONE

   Y7 := F7 (1); -- @TERMINATION:FAIL
   Y8 := F8 (1); -- @TERMINATION:NONE
   Y9 := F9 (1); -- @TERMINATION:PASS
   Y9 := F9 (-1); -- @TERMINATION:FAIL

   G := 42;
   Y10 := F10 (1);
   pragma Assert (G = 42); -- @ASSERT:FAIL

   G := 42;
   Y11 := F11 (1);
   pragma Assert (G = 42); -- @ASSERT:FAIL

end OK_Call;
