package P with
    Abstract_State => State,
    Initializes    => State
is
   procedure Proc (X : out Boolean) with
     Depends => (X => State, State => null);
   --  This contract is intentionally complete (i.e. includes all inputs and
   --  outputs), but wrong (i.e. it doesn't include "State => State" clause).
   --
   --  The error message must be phrased in terms of abstract view (State),
   --  but the code path must be discovered in terms of its refined view (A).
end;
