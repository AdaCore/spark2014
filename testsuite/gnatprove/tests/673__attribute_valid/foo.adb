procedure Foo (X : Integer) with SPARK_Mode is
begin
   pragma Assert (not X'Valid or else X /= 0); --@ASSERT:FAIL
end Foo;
