package Swap_Incorrect_D
  with SPARK_Mode
is

   procedure Swap (X : in out Integer;
                   Y : in out Integer)
     with Global => null,
          Depends => (X => Y,
                      Y => X);

end Swap_Incorrect_D;
