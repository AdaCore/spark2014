with Pairs.Additional;

--  Confirm that inherit clause not needed.

package Pair_State
with
   Abstract_State => State;
is
   procedure Increment_State;
   with
      Global  => (In_Out => State),
      Depends => (State => State);

end Pair_State;

