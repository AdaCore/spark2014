package P
  with SPARK_Mode
is
   type A is array (Positive range <>) of Integer;

   -- Shows that X'First, X'Last and X'Length _can_ be used
   -- in precondition here, even though X is mode "out"...
   procedure Init (X : out A)
     with Pre  => X'First = 1 and X'Last >= 20,
          Post => (for all I in X'Range =>
                     (if I = 1 then X (I) = X'Last
                      elsif I = 20 then X (I) = -1
                      else X (I) = 0));
end P;
