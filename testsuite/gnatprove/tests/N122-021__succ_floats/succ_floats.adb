procedure Succ_Floats (A, B : Boolean) is
   X : Float;
begin
   X := 0.0;
   pragma Assert (Float'Succ (X) > 0.0); -- @ASSERT:PASS
   pragma Assert (Float'Succ (X) < 1.0); -- Assert is true: provers timeout
   pragma Assert (Float'Pred (X) < 0.0); -- @ASSERT:PASS
   pragma Assert (Float'Pred (X) > -1.0); -- @ASSERT:PASS

   X := 1.0;
   pragma Assert (Float'Succ (X) > 1.0); -- @ASSERT:PASS
   pragma Assert (Float'Succ (X) < 1.1); -- Assert is true: provers timeout
   pragma Assert (Float'Pred (X) < 1.0); -- @ASSERT:PASS
   pragma Assert (Float'Pred (X) > 0.9); -- Assert is true: provers timeout

   X := Float'Last;
   if A then
      X := Float'Succ (X); -- @FLOAT_OVERFLOW_CHECK:FAIL
   else
      pragma Assert (Float'Pred (X) < Float'Last); -- @ASSERT:PASS
   end if;
   pragma Assert (Float'Pred (X) > 0.0); -- @ASSERT:PASS

   X := Float'First;
   if B then
      X := Float'Pred (X); -- @FLOAT_OVERFLOW_CHECK:FAIL
   else
      pragma Assert (Float'Succ (X) > Float'First); -- @ASSERT:PASS @FLOAT_OVERFLOW_CHECK:PASS
   end if;
   pragma Assert (Float'Succ (X) < 0.0);
end Succ_Floats;
