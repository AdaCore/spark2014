with P1;
with P3.Child;
package P2 with SPARK_Mode is
   function My_True (V : P1.C) return Boolean is (P1.All_In (V))
   with Post => My_True'Result;
   function My_True (V : P3.Child.C) return Boolean is (P3.Child.All_In (V))
   with Post => My_True'Result;
end P2;
