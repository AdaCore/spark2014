package body Swap_Incorrect_B
is

   Call_Count : Natural := 0;

   procedure Swap (X : in out Integer;
                   Y : in out Integer)
   is
      Old_X : Integer := X;
   begin
      X := Y;
      Y := Old_X;

      Call_Count := Call_Count + 1;
   end Swap;

end Swap_Incorrect_B;
