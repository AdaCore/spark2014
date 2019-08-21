procedure Generic_Increment (X : in out T) with
  SPARK_Mode
is
begin
   X := X + 1;
end Generic_Increment;
