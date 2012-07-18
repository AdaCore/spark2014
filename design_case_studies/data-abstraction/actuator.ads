-- This is an extended version of the Actuator package from the
-- Heating Controller example from the SPARK SWEWS course to demonstrate
-- having the state abstraction of the package Actuator.State being distributed
-- across its two private children.
-- It also demonstrates the calling of subprograms which operate on constituents
-- which are themselves state abstractions.
-- It is not intended to be an ideal way of implementing this package.
package Actuator
with
  Abstract_State => State,
  Initial_Condition => Status = Unknown
is
   type Status_T (Off, On, Unknown);

   function Status return Status_T
   with
     Global_In => State;

   procedure TurnOn
   with
     Global_In_Out => State,
     Derives => (Outputs => Null);
     -- Turns the heating on.

   procedure TurnOff
   with
     Global_In_Out => State,
     Derives => (Outputs => Null);
     -- Turns the heating off.

end Actuator;
