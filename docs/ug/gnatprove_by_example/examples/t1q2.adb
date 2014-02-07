package body T1Q2
  with SPARK_Mode
is

   procedure Increment2 (X, Y : in out Integer) is
      X_Old : constant Integer := X;
      Y_Old : constant Integer := Y;
   begin
      X := X + 1;
      pragma Assert_And_Cut ((X = X_Old + 1) and (Y = Y_Old));
      Y := Y + 1;
   end Increment2;

end T1Q2;
