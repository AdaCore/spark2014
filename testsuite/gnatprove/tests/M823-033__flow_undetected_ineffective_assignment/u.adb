procedure U (M : in out Integer)
is
   X : Integer;

   procedure A (Z: in out Integer)
   with Global => (Output => X),
        Depends => ((X, Z) => Z)
   is
   begin
      X := 2 * Z;
      Z := X;
   end A;
begin
   A (M);
   A (M);
end U;
