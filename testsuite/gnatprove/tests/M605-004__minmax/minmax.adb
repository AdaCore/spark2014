package body Minmax is

   procedure P (A, B : Float;
                C    : out Float;
                X, Y : Integer;
                Z    : out Integer)
   is
   begin
      C := Float'Min (A, B);
      C := Float'Max (A, B);
      Z := Integer'Max (X, Y);
      Z := Integer'Max (X, Y);
   end P;
end Minmax;
