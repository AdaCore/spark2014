package Actuator
  with Abstract_State => (Outputs with External => Async_Readers)
is
   -- We don't know anything about how type Settings is implemented but we do
   -- need a type declaration for it so that we can declare proof functions
   -- that use it. The following proof type declaration does what we need.
   --# type Settings is abstract;
   -- and allows us to define this proof function
   function IsOn return Boolean
     with Global => Outputs;

   procedure TurnOn
     with Global  => (Output => Outputs),
          Depends => (Outputs => null),
          Post    => IsOn;
   -- Turns the heating on.

   procedure TurnOff
     with Global  => (Output  => Outputs),
          Depends => (Outputs => null),
          Post    => not IsOn;
   -- Turns the heating off.
end Actuator;
