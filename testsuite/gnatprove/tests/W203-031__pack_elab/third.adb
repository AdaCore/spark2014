procedure Third
  with
    SPARK_Mode => On
is

   function Id (X : Integer) return Integer is (X);

   subtype T is Integer range Id (1) .. Id (2);

   C : constant T := Id (3); --@RANGE_CHECK:FAIL

   function F return Boolean is (True) with
     Post => F'Result = (Id (1) <= C and C <= Id (2));
   B : constant Boolean := F;

begin
   null;
end Third;
