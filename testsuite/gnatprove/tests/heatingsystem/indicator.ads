package Indicator
  with Abstract_State => (Outputs with External => Async_Readers)
is
   --# type Settings is abstract;
   function IsOn return Boolean
     with Global => Outputs;

   procedure TurnOn
     with Global  => (Output  => Outputs),
          Depends => (Outputs => null),
          Post    => IsOn;
   -- Turns the indicator on.

   procedure TurnOff
     with Global  => (Output  => Outputs),
          Depends => (Outputs => null),
          Post    => not IsOn;
   -- Turns the indicator off.

end Indicator;
