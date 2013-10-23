package body T1Q3A
is
   pragma SPARK_Mode;

   procedure Swap (X, Y: in out Integer)
   is
      Temp : Integer;
   begin
      Temp := X;
      X := Y;
      Y := Temp;
   end Swap;

end T1Q3A;
