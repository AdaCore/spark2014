package Pack
  with
    SPARK_Mode => On
is

   function Id (X : Integer) return Integer is (X);

   function F return Boolean is (True) with
     Post => F'Result = (Id (1) <= C and C <= Id (2));

   subtype T is Integer range Id (1) .. Id (2);

   C : constant T := Id (3); --@RANGE_CHECK:FAIL
   B : constant Boolean := F;
end Pack;
