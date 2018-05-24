package body Q with Refined_State => (State1 => B,
                                      State2 => C)
is
   procedure Initialize
     with Refined_Global => (Output => (B, C))
   is
   begin
      B := 0;
      C := 0;
   end Initialize;
end Q;
