package body Interval_Reasoning
is
   procedure Propagation_Loop (X, Y, Z : in Large_Range)
     with Depends => (null => (X, Y, Z)),
          Pre     => X < Y and Y < Z and Z < X
   is
   begin
      pragma Assert (False);  --  @ASSERT:PASS
   end Propagation_Loop;
end Interval_Reasoning;
