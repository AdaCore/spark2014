package Repro.C
with
  Abstract_State    => State,
  Initializes       => State,
  Initial_Condition => Invariant
  --  Repro.State is read in Initial_Condition, but can't be represented in the
  --  Initializes contract until we allow "null => ..." clauses there.
is

   function Invariant return Boolean
   with
     Ghost,
     Global => (Input => (State, Repro.State));

end Repro.C;
