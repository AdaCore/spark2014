package body Q.Priv.Pub
  --  Refined_State is required
  with Refined_State =>
  (Pubs_State => C) is
    --  Test line: Uncomment to check that D
    --  should *not* be part of the state.
    --  (Pubs_State => (C,D)) is
    procedure Dummy is null;
end;
