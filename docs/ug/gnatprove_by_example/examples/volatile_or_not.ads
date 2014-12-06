package Volatile_Or_Not with
  SPARK_Mode,
  Initializes => V
is
   V : Integer with Volatile;
   N : Integer;

   procedure Swap_Then_Zero with
     Global  => (In_Out => (N, V)),
     Depends => (V => N, N => null, null => V);

end Volatile_Or_Not;
