package body Stone is

   Z : Integer;
   procedure Incr (X : in out Integer) is
   begin
      Z := X;
      X := Z + 1;
   end Incr;

end Stone;
