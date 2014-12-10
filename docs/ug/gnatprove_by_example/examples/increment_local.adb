procedure Increment_Local with
  SPARK_Mode
is
   procedure Increment (X : in out Integer) is
   begin
      X := X + 1;
   end Increment;

   X : Integer;

begin
   X := 0;
   Increment (X);
   Increment (X);
   pragma Assert (X = 2);
end Increment_Local;
