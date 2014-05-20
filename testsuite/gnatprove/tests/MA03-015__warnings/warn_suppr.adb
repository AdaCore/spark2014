package body Warn_Suppr is

   procedure P (X, Y : Integer) is
      Z, K : Integer := 0;
   begin
      Z := X + Y;
      pragma Warnings(Off, "overflow check",
                      Reason =>"deliberately ignored");
      K := X * Y;
      pragma Warnings(On, "overflow check");
      Z := Z + K;
   end P;

end Warn_Suppr;
