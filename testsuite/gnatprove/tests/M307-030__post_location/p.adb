procedure P is
   procedure Q (X, Y : out Integer) with
     Post => X >= 0
               and then
             Y >= 0;

   procedure Q (X, Y : out Integer) is
   begin
      X := -1;
      Y := 3;
   end Q;

   X, Y : Integer;
begin
   Q (X, Y);
end P;
