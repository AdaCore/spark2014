procedure Mem
  with SPARK_Mode
is
   type Root is tagged null record;
   type Derived is new Root with null record;

   X : Derived;

   function Test_Mem (V : Root'Class) return Boolean is (V in Derived);
   function Test_Mem_Class (V : Root'Class) return Boolean is (V in Derived'Class);
begin
   pragma Assert (Test_Mem (Root'Class(X)));
   pragma Assert (Test_Mem_Class (Root'Class(X)));
end Mem;
