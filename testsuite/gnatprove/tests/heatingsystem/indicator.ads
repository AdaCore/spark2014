package Indicator
  with Abstract_State => (Outputs with External => Async_Readers)
is
   procedure TurnOn
     with Global  => (Output  => Outputs),
          Depends => (Outputs => null);
   -- Turns the indicator on.

   procedure TurnOff
     with Global  => (Output  => Outputs),
          Depends => (Outputs => null);
   -- Turns the indicator off.

end Indicator;
