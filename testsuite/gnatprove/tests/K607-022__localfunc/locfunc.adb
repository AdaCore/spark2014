package body Locfunc is
   procedure P (X : in out Integer) is
      Y : Integer;

      procedure Q
        with Global => (Output => (X, Y)),
             Post => (X = 0 and then Y = 0);

      procedure Q is
      begin
         X := 0;
         Y := 0;
      end;

   begin
      Q;
   end P;
end Locfunc;
