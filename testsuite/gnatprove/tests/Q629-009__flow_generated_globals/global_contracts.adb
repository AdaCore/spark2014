with Global_Contracts.State;

package body Global_Contracts with
  Refined_State => (S1 => (State.B1, State.B2), S2 => State.G)
is
end Global_Contracts;
