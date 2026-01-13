pragma Extensions_Allowed (All_Extensions);
procedure Main with SPARK_Mode is
   type U is range 0 .. 2 ** 16 - 1 with Unsigned_Base_Range;
   procedure Pre_OK (X : U) with Pre => (X ** 40 >= 3); --@OVERFLOW_CHECK:NONE
   procedure Pre_OK (X : U) is null;
begin
   Pre_OK (3);
end Main;
