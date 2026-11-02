package body Opaque_Specialization with SPARK_Mode is
   function Wrapped return Integer is
   begin
      return Eval (Read'Access);
   end Wrapped;

   function Wrapped_Visible return Integer is
   begin
      return Eval (Read_Visible'Access);
   end Wrapped_Visible;

   procedure Check is
   begin
      --  Both calls read the same opaque state, whose value is unknown

      pragma Assert (Wrapped = Read); -- @ASSERT:PASS
      pragma Assert (Wrapped = 0); -- @ASSERT:FAIL
   end Check;

   procedure Check_Change is
      Before : constant Integer := Wrapped;
   begin
      Change;

      --  Change may modify the opaque state, so equality with Before is no
      --  longer guaranteed.

      pragma Assert (Wrapped = Before); -- @ASSERT:FAIL
   end Check_Change;

   procedure Check_Visible is
      Before : Integer;
   begin
      --  Calls must read the current Visible, including after an assignment

      Visible := 1;
      Before := Wrapped_Visible;
      pragma Assert (Before = 1); -- @ASSERT:PASS
      Visible := 2;
      pragma Assert (Wrapped_Visible = 2); -- @ASSERT:PASS
      pragma Assert (Wrapped_Visible = Before); -- @ASSERT:FAIL
   end Check_Visible;
end Opaque_Specialization;
