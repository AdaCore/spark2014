pragma SPARK_Mode;

with Globals;

package State with
  Abstract_State => State
is

   procedure Test
   with
     Global => (Output => State,
                Input => Globals.Val),
     Depends => (State => Globals.Val);

end State;
