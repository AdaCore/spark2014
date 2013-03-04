package body Test is

   procedure Swap_01 (X, Y : in out Integer)
     with Depends => (X => Y,
                      Y => X);

   procedure Swap_01 (X, Y : in out Integer)
   is
   begin
      X := Y;
      Y := X;
      --  Well, of course this won't work.
   end Swap_01;

end Test;
