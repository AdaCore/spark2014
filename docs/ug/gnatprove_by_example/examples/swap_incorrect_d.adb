package body Swap_Incorrect_D
is
   pragma SPARK_Mode;

   procedure Swap (X : in out Integer;
                   Y : in out Integer)
   is
      Old_X : Integer := X;
      Old_Y : Integer;
   begin
      X := Old_Y;
      Y := Old_X;
   end Swap;

end Swap_Incorrect_D;
