procedure Repr with SPARK_Mode is

   type T is new Integer with Default_Value => 0;
   type A is access T;
   pragma Assert (A'(new T) = null);--@ASSERT:FAIL @MEMORY_LEAK:FAIL
begin
   null;
end Repr;
