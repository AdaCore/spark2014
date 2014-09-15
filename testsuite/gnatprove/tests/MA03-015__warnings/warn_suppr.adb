package body Warn_Suppr is

   procedure P (X, Y : Integer) is
      Z, K : Integer := 0;
   begin
      Z := X + Y;
      pragma Annotate(Gnatprove, Intentional, "overflow check", "deliberately ignored");
      K := X * Y;
      Z := Z + K;
   end P;

end Warn_Suppr;
