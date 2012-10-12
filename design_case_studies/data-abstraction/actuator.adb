-- In the body of Actuator the state abstraction Actuator.State is refined in two
-- constituents, both of which are state abstractions of its private children.
-- The subprograms of Actuator are defined in terms of calls to subprograms of
-- its children which each work on part of the overall state abstraction
-- Actuator.State.
-- An interesting point is the Initial_Condition of Actuator which is given
-- in terms of its function Status.  The specification (and implementation) of
-- Status is actually a call of the function Mirror.Get_State.
-- The Initial_Condition of Actuator.Mirror.State is given in terms of
-- Actuator.Mirror.State. We will need to be able to prove that
-- Actuator.Mirror.Get_State = Actuator.Unknown ->
--    Actuator.Status = Actuator.Uknown.
with Actuator.Mirror,
     Actuator.Raw;
package body Actuator
with
Refined_State => (State => (Actuator.Raw.Outputs => (Volatile => Output)),
                            Actuator.Mirror.State)
is
   function Status return Status_T is (Mirror.Get_State);

   procedure TurnOn
   with
     Refined_Global =>
       (In_Out => Mirror.State,
        Output => Raw.Outputs),
     Refined_Depends =>
       ((Mirror.State, Raw.Outputs) => Mirror.State)
   is
      if Mirror.Get_State /= Actuator.On then
         Mirror.Set_State (Actuator.On);
         Raw.Set (Actuator.On);
      end if;
   end Turn_On;

   procedure TurnOff
   with
     Refined_Global =>
       (In_Out => Mirror.State,
        Output => Raw.Outputs,
        Refined_Depends =>
          ((Mirror.State, Raw.Outputs) => Mirror.State)
   is
      if Mirror.Get_State /= Actuator.Off then
         Mirror.Set_State (Actuator.Off);
         Raw.Set (Actuator.Off);
      end if;
   end Turn_Off;

end Actuator;
