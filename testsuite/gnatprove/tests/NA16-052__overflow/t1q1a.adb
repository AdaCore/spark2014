package body T1Q1A
  with SPARK_Mode
is

   procedure Increment (X : in out Integer) is
   begin
      X := X + 1;
   end Increment;

end T1Q1A;
