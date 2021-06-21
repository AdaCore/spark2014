package body Volatile_Or_Not with
  SPARK_Mode
is
   procedure Swap_Then_Zero is
      Tmp : constant Integer := V;
   begin
      --  Swap values of V and N
      V := N;
      N := Tmp;
      --  Zero out values of V and N
      V := 0;
      N := 0;
   end Swap_Then_Zero;

end Volatile_Or_Not;
