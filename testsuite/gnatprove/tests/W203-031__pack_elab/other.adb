procedure Other
  with
    SPARK_Mode => On
is

   function Id (X : Integer) return Integer is (X);

   function F return Boolean is (True) with
     Post => F'Result = (T2'First > T2'Last or else (T (Id (1)) <= T2'Last and T2'Last <= T (Id (2)))); --@POSTCONDITION:FAIL

   type T is new Integer range 1 .. 2;

   B : constant Boolean := F;

   subtype T2 is T range T (Id (1)) .. T'Base (Id (3));

begin
   null;
end Other;
