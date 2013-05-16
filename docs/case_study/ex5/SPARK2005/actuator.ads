package Actuator
--# own out Outputs : Settings;
is
   -- We don't know anything about how type Settings is implemented but we do need a type
   -- declaration for it so that we can declarae proof functions that use it.  The following
   -- proof type declaration does what we need.
   --# type Settings is abstract;

   -- and allows us to define this proof function
   --# function IsOn (S : Settings) return Boolean;

   procedure TurnOn;
   --# global  out Outputs;
   --# derives Outputs from ;
   --# post IsOn (Outputs); -- making use of the proof function declared above
   --
   -- Turns the heating on.

   procedure TurnOff;
   --# global  out Outputs;
   --# derives Outputs from ;
   --# post not IsOn (Outputs);
   --
   -- Turns the heating off.
end Actuator;
