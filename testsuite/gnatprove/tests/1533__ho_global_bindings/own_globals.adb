package body Own_Globals with SPARK_Mode is
   function Wrapped return Boolean is
   begin
      return Eval (Always_False'Access);
   end Wrapped;

   procedure Check is
   begin
      Flag := False;
      pragma Assert (not Wrapped); -- @ASSERT:PASS
      Flag := True;
      pragma Assert (Wrapped); -- @ASSERT:PASS

      --  The result must reflect the updated Flag rather than its old value

      pragma Assert (not Wrapped); -- @ASSERT:FAIL
   end Check;
end Own_Globals;
