package body Minmax is

   procedure P is
      A, B, C : Float;
      X, Y, Z : Integer;
   begin
      C := Float'Min (A, B);
      C := Float'Max (A, B);
      Z := Integer'Max (X, Y);
      Z := Integer'Max (X, Y);
   end P;
end Minmax;
