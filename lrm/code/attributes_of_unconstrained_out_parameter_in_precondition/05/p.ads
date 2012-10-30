package P
is
   type A is array (Positive range <>) of Integer;

   -- Shows that X'First, X'Last and X'Length _can_ be used
   -- in precondition here, even though X is mode "out"...
   procedure Init (X : out A);
   --# derives X from ;
   --# pre X'First <= 2 and
   --#   X'Last >= 20 and
   --#   X'Length >= 19;
   --# post for all I in Positive range X'First .. X'Last => (X (I) = 0);

end P;
