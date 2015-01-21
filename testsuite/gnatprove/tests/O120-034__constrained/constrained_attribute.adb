package body Constrained_Attribute with SPARK_Mode is
   procedure Test is
      A : Mut_Rec := (D => 0, others => <>);
      B : Mut_Rec (0) := A;
   begin
      pragma Assert (B'Constrained);
      pragma Assert (Is_Constrained (B));
      pragma Assert (not A'Constrained);
      pragma Assert (not Is_Constrained (A)); --@ASSERT:FAIL
   end Test;
end;
