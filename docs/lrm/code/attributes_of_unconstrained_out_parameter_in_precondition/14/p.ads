package P is
   type A is array (Positive range <>) of Integer;

   -- Shows that X'First, X'Last and X'Length _can_ be used
   -- in precondition here, even though X is mode "out"...
   procedure Init (X : out A)
     with Depends => (X => null),
          Pre     => X'First <= 2 and X'Last >= 20,
          Post    => (for all I in X'Range => (X (I) = 0));
end P;
