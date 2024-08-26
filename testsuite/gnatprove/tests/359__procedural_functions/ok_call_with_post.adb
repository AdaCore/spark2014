pragma Warnings (Off);

with P_With_Post; use P_With_Post;

procedure OK_Call_With_Post with
  SPARK_Mode,
  Always_Terminates => True
is
   Y0, Y1, Y2, Y3, Y4, Y5, Y6, Y7, Y8, Y9, Y10, Y11 : Integer := 42;

   function Rand return Integer with Import;

begin
   Y1 := F1 (Y0);
   pragma Assert (Y0 = 0); -- @ASSERT:PASS
   pragma Assert (Y1 = 0); -- @ASSERT:PASS

   Y0 := 42;
   Y2 := F2 (Y0);
   pragma Assert (Y0 = 0); -- @ASSERT:PASS
   pragma Assert (Y2 = 0); -- @ASSERT:PASS

   G := 42;
   Y3 := F3 (1);
   pragma Assert (G = 1); -- @ASSERT:PASS
   pragma Assert (Y3 = 1); -- @ASSERT:PASS

   G := 42;
   Y4 := F4 (1);
   pragma Assert (G = 1); -- @ASSERT:PASS
   pragma Assert (Y4 = 1); -- @ASSERT:PASS

   Y5 := F5 (1); -- @RAISE:PASS
   pragma Assert (Y5 = 1); -- @ASSERT:PASS

   Y6 := F6 (1); -- @RAISE:NONE
   pragma Assert (Y6 = 1); -- @ASSERT:PASS

   if Rand = 1 then
      Y7 := F7 (1); -- @TERMINATION:FAIL
      pragma Assert (False); -- @ASSERT:PASS
   end if;

   Y8 := F8 (1); -- @TERMINATION:NONE
   pragma Assert (Y8 = 1); -- @ASSERT:PASS

   Y9 := F9 (1); -- @TERMINATION:PASS
   pragma Assert (Y9 = 1); -- @ASSERT:PASS

   if Rand = 2 then
      Y9 := F9 (-1); -- @TERMINATION:FAIL
      pragma Assert (False); -- @ASSERT:PASS
   end if;

   G := 42;
   Y10 := F10 (1);
   pragma Assert (G = 1); -- @ASSERT:PASS
   pragma Assert (Y10 = 1); -- @ASSERT:PASS

   G := 42;
   Y11 := F11 (1);
   pragma Assert (G = 1); -- @ASSERT:PASS
   pragma Assert (Y11 = 1); -- @ASSERT:PASS

end OK_Call_With_Post;
