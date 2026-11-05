procedure Main (X : Integer) with SPARK_Mode is
begin
   pragma Assume (X > 0);
   pragma Assert (X >= 0);
end Main;
