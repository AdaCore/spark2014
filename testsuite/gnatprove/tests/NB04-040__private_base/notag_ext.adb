package body Notag_Ext with
  SPARK_Mode
is
   procedure Test is
      A : constant U := Create (1);
      B : constant U := Create (2);
   begin
      pragma Assert (Sum(T(A)) /= Sum(T(B)));  --  @ASSERT:PASS
   end Test;
end Notag_Ext;
