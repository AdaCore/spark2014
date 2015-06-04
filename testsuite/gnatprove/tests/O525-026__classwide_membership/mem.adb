procedure Mem
  with SPARK_Mode
is
   type Root is tagged null record;
   type Derived is new Root with null record;

   X : Derived;

   function Test_Mem (V : Root'Class) return Boolean is (V in Derived);
   function Test_Mem_Class (V : Root'Class) return Boolean is (V in Derived'Class);
   function Test_Mem_Class1 (V : Root'Class) return Boolean is (V in Derived'Class | Derived);
   function Test_Mem_Class2 (V : Root'Class) return Boolean is (V in Derived | Derived'Class);
begin
   pragma Assert (Test_Mem (Root'Class(X)));
   pragma Assert (Test_Mem_Class (Root'Class(X)));
   pragma Assert (Test_Mem_Class1 (Root'Class(X)));
   pragma Assert (Test_Mem_Class2 (Root'Class(X)));
end Mem;
