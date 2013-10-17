package Swap_Incorrect_C
is
   pragma SPARK_Mode;

   procedure Swap (X : in out Integer;
                   Y : in out Integer)
     with Global => null,
          Depends => (X => Y,
                      Y => X);

end Swap_Incorrect_C;
