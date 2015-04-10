-- The body of Actuator.Mirror refines the state abstraction
-- Actuator.Mirror.State on to a single constituent State.
-- This is a one-to-one mapping.
package body Actuator.Mirror
with
  Abstract_Refinement => (State => State)
is
   State : Actuator.Status_T := Actuator.Unknown;

   function Get_State return Actuator.Status_T is (State);

   procedure Set_State (S : in Actuator.Status_T)
   is
   begin
      State := S;
   end Set_State;

send Actuator.Mirror;


