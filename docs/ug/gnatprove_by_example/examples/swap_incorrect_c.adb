package body Swap_Incorrect_C
is

   procedure Swap (X : in out Integer;
                   Y : in out Integer)
   is
      Old_X : Integer := X;
      Old_Y : Integer;
   begin
      Old_X := X;
      X := Y;
      Y := Old_X;
   end Swap;

end Swap_Incorrect_C;
