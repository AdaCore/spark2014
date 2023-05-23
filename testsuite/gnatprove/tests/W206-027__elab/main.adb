procedure Main (X : Integer)
  with
    SPARK_Mode => On
is

   function F return Boolean is (True) with
     Post => F'Result = (X /= Integer'Last and C = X + 1);

   Y : constant Boolean := F;
   C : constant Integer := X + 1; --@RANGE_CHECK:FAIL
begin
   pragma Assert (X < Integer'Last);
end Main;
