package body Gen_Unit is

   function Target (X : Integer) return Integer is (X) with Pre => True, SPARK_Mode => Off;

   function F (X : Integer) return Integer is
   begin
      return 2 / Target (X);
   end F;

end Gen_Unit;
