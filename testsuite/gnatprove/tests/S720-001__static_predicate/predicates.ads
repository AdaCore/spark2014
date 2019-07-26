package Predicates with SPARK_Mode is

   subtype T1 is Float with Static_Predicate => T1 /= 0.0;

   X0 : constant Float := 0.0;
   X1 : constant Float := 1.0;

   function Test1 (X : Float) return Boolean is (X in T1);

   pragma Assert (not Test1 (X0));  -- @ASSERT:PASS
   pragma Assert (Test1 (X1));      -- @ASSERT:PASS

   subtype T2 is String with Static_Predicate => T2 in "titi" | "toto";

   Y0 : constant String := "tutu";
   Y1 : constant String := "toto";

   function Test2 (X : String) return Boolean is (X in T2);

   pragma Assert (not Test2 (Y0));  -- @ASSERT:PASS
   pragma Assert (Test2 (Y1));      -- @ASSERT:PASS

end Predicates;
