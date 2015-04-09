with Private_With_Attributes; use Private_With_Attributes;
with Public_Derives_Private;  use Public_Derives_Private;

package body Use_Private_Attributes with SPARK_Mode is
   procedure Test_Constrained (U : in out Private_Unconstrained) is
      U1: Private_Unconstrained;
      U2: Private_Unconstrained (C => 0);
      C : Private_Constrained;
   begin
      pragma Assert (U'Constrained);
      pragma Assert (not U1'Constrained);
      pragma Assert (U2'Constrained);
      pragma Assert (C'Constrained);
      U1 := U;
      U2 := U1; --@DISCRIMINANT_CHECK:FAIL
      C := U1;
      pragma Assert (not U1'Constrained);
      pragma Assert (U2'Constrained);
      pragma Assert (C'Constrained);
   end Test_Constrained;

   procedure Test_Tag (C : Natural) is
      R : Root_Private_Tagged;
      F : Child_Private_Tagged;
      G : Grand_Child_Private_Tagged;
      P : Private_Grand_Child_Private_Tagged;
      RC : Root_Private_Tagged'Class := R;
      FC : Root_Private_Tagged'Class := F;
      G1 : Grand_Child := (C1 with F2 => 1);
      G2 : Grand_Child := (C2 with F2 => 1);
   begin
      pragma Assert (C1 /= C2); --@ASSERT:FAIL
      pragma Assert (C1.F = C2.F); --@ASSERT:FAIL
      pragma Assert (RC /= FC);
      pragma Assert (Root (G1) = Root (G2));
      pragma Assert (Get_F2 (P) = 0);
   end Test_Tag;
end Use_Private_Attributes;
