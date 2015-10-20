package body RT is

   procedure P1 (X : out Boolean) is
      T1, T2 : Time;
   begin
      T1 := Clock;
      T2 := Clock;

      -- should NOT prove, since Clock accesses volatile state
      pragma Assert (T1 = T2);  -- @ASSERT:FAIL

      X := T1 = T2;
   end P1;

end RT;
