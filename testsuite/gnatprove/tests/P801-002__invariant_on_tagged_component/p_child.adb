package body P_Child with SPARK_Mode is
   function Test (X : Child) return Natural is
      Bad : Child := X;
   begin
      Bad.G := 0;
      return F (Root'Class (Bad)); --@INVARIANT_CHECK:FAIL
   end Test;
end P_Child;
