-- This private child introduces a state abstraction representing an
-- external output and a subprogram to set it to a particular mode.
private package Actuator.Raw
with
  Abstract_State => (Outputs => Volatile_Out)
is
   subtype On_Off is Actuator.Status_T range (Actuator.On .. Actuator.Off);

   procedure Set (On_Or_Off : in On_Off)
   with
     Global_Out => Outputs,
     Derives => (Outputs => On_Or_Off);

end Actuator.Raw;
