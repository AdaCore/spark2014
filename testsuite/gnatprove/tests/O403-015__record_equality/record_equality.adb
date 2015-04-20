package body Record_Equality with SPARK_Mode is
   procedure Test_Eq_Ok is
      R_Pu1 : Root (0);
      R_Pu2 : Root_0;
      C_Pu1 : Child (0);
      C_Pu2 : Child_0;
      G_Pu1 : GrandChild := (C_Pu1 with F3 => 0);
      G_Pu2 : GrandChild := (C_Pu1 with F3 => 1);
      C_GP1 : constant Child := Child (G_Pu1);
      C_GP2 : constant Child (0) := Child (G_Pu2);
   begin
      pragma Assert (R_Pu1 = R_Pu2);
      pragma Assert (Root (C_Pu1) = Root (C_Pu2));
      pragma Assert (Child (G_Pu1) = Child (G_Pu2));
      pragma Assert (C_GP1 = C_GP2);
      pragma Assert (G_Pu1 /= G_Pu2);
      pragma Assert (C_Pu1 = C_Pu2);
      pragma Assert (Root'Class (R_Pu1) /= Root'Class (C_Pu1));
   end Test_Eq_Ok;
   procedure Test_Eq_Ko is
      C_Pu1 : Child (0);
      G_Pu1 : GrandChild := (C_Pu1 with F3 => 0);
      G_Pu2 : GrandChild := (C_Pu1 with F3 => 1);
   begin
      pragma Assert (G_Pu1 = G_Pu2); --@ASSERT:FAIL
   end Test_Eq_Ko;
   procedure Test_Eq_Ko_D is
      R_Pu1 : Root (0);
      C_Pu1 : Child (0);
   begin
      pragma Assert (Root'Class (R_Pu1) = Root'Class (C_Pu1)); --@ASSERT:FAIL
   end Test_Eq_Ko_D;
   procedure Test_Eq_Ko_D2 is
      C_Pu1 : Child (0);
      G_Pu1 : GrandChild := (C_Pu1 with F3 => 0);
      G_Pu2 : GrandChild := (C_Pu1 with F3 => 1);
   begin
      pragma Assert (Root'Class (G_Pu1) = Root'Class (G_Pu2)); --@ASSERT:FAIL
   end Test_Eq_Ko_D2;
   procedure Test_Eq_Ko_D3 is
      C_Pu1 : Child (0);
      G_Pu1 : GrandChild := (C_Pu1 with F3 => 0);
      G_Pu2 : GrandChild := (C_Pu1 with F3 => 1);
      R_G1  : Root'Class := Root'Class (G_Pu1);
      R_G2  : Root'Class := Root'Class (G_Pu2);
   begin
      pragma Assert (R_G1 = R_G2); --@ASSERT:FAIL
   end Test_Eq_Ko_D3;
end Record_Equality;
