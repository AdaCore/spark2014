procedure Unref with
  SPARK_Mode
is
   X : Integer;
   pragma Unreferenced (X);
begin
   X := 10;
end Unref;
