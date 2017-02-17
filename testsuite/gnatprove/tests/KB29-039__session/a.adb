package body A is

   procedure P (X, Y : Integer) is
   begin
      pragma Assert (X < Y);
      pragma Assert (X + 1 < Y);
   end P;

end A;
