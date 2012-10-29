-- This child package introduces a state abstraction which mirrrors the
-- Actuator mode.
-- Subprograms which operate on the state abstraction are also declared.
-- The initial condition states that the mode of the Actuator is Unknown.
private package Actuator.Mirror
with
  Abstract_State => State,
  Initializes => State,
  Initial_Condition => Get_State = Actuator.Unknown
is
   function Get_State return Actuator.Status_T
   with
     Global => State;

   procedure Set_State (S : in Actuator.Status_T)
   with
     Global  => (In_Out => State),
     Depends => (State => S);

send Actuator.Mirror;


