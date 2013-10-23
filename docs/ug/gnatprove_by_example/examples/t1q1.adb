package body T1Q1
is
   pragma SPARK_Mode;

   procedure Increment (X: in out Integer)
   is
   begin
      X := X + 1;
   end Increment;

end T1Q1;

