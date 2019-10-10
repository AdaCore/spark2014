with Test_2; use Test_2;
procedure Use_Test with SPARK_Mode is
   X : Context_Type; --@DEFAULT_INITIAL_CONDITION:PASS
   Y : Context_Type (1, 1); --@DEFAULT_INITIAL_CONDITION:FAIL
begin
   null;
end Use_Test;
