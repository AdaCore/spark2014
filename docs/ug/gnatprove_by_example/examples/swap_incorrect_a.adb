package body Swap_Incorrect_A
is

   procedure Swap (X : in out Integer;
                   Y : in out Integer)
   is
   begin
      X := Y;
      Y := X;
   end Swap;

end Swap_Incorrect_A;
