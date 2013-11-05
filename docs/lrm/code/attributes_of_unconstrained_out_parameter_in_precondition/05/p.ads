package P
is
   type A is array (Positive range <>) of Integer;

   -- Shows that X'First and X'Last _can_ be used in
   -- precondition here, even though X is mode "out"...
   procedure Init (X : out A);
   --# pre X'First = 1  and
   --#     X'Last  >= 20;
   --# post for all I in Positive range X'Range =>
   --#      ((I /= 20 -> (X (I) = 0)) and
   --#         (I = 1 -> (X (I) = X'Last)) and
   --#         (I = 20 -> (X (I) = -1)));

end P;
