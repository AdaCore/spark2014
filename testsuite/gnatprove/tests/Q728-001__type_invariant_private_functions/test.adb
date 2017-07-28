with Test_Type; use Test_Type;
procedure Test with SPARK_Mode is
   X : T;
   Y : T := Decr (X);
begin
   pragma Assert (X /= Y); --@ASSERT:FAIL
end Test;
