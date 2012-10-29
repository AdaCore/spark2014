package body Pair_State
is

   State : Pairs.Pair;

   procedure Increment_State
   is
   begin
      Pairs.Additional.Increment (State);
   end Increment_State;

end Pair_State;

