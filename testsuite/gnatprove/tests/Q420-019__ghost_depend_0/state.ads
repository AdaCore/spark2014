pragma SPARK_Mode;

package State with
  -- Ghost,   -- [2]
  Abstract_State => State,
  Initializes => State
is

   procedure Test
     with Ghost,
     Global => (In_Out => State);
     -- Depends => (State => State); -- [1]

private

   S : Integer := 0
     with Ghost, Part_Of => State;

end State;
