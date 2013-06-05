package P
is
   type A is array (Positive range <>) of Integer;

   -- Shows that X'First and X'Last _can_ be used in
   -- precondition here, even though X is mode "out"...
   procedure Init (X : out A);
   --# derives X from ;
   --# pre X'First <= 2  and
   --#     X'Last  >= 20;
   --# post for all I in Positive range X'Range => (X (I) = 0);

end P;
