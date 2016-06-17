package body Outer
  with Refined_State => (A2 => (Private_State, State_In_Body))
is
   State_In_Body : Integer;

   procedure Init_A2
     with Refined_Global  => (Output => (Private_State, State_In_Body))
   is
   begin
      Private_State := 0;
      State_In_Body := 42;
   end Init_A2;

end Outer;
