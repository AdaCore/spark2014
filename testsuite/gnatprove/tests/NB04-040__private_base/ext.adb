package body Ext with
  SPARK_Mode
is
   procedure Test is
      A : constant U := Create (1);
      B : constant U := Create (2);
   begin
      pragma Assert (T(A).Sum = T(B).Sum);  --  @ASSERT:FAIL
   end Test;
end Ext;
