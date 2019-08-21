procedure Test_Tag with SPARK_Mode is
   type Root is tagged record
      F : Integer := 0;
   end record;

   type Child is new Root with record
      G : Integer := 0;
   end record;

   type R_Acc is access Root;
   type RC_Acc is access Root'Class;

   procedure Test_Uninit_1 is
      X : RC_Acc := new Root;
   begin
      pragma Assert (X.all not in Root); --@ASSERT:FAIL
   end Test_Uninit_1;

   procedure Test_Uninit_2 is
      Y : RC_Acc := new Child;
   begin
      pragma Assert (Y.all not in Child); --@ASSERT:FAIL
   end Test_Uninit_2;

   procedure Test_Uninit_3 is
      Z : R_Acc := new Root;
   begin
      pragma Assert (Z.all not in Root); --@ASSERT:FAIL
   end Test_Uninit_3;

   procedure Test_Uninit_4 is
      X : RC_Acc := new Root;
      Y : RC_Acc := new Child;
      Z : R_Acc := new Root;
   begin
      pragma Assert (X.all in Root);
      pragma Assert (Y.all in Child);
      pragma Assert (Z.all in Root);
   end Test_Uninit_4;

   procedure Test_Init_1 is
      R : Root;
      X : RC_Acc := new Root'Class'(Root'Class (R));
   begin
      pragma Assert (X.all not in Root); --@ASSERT:FAIL
   end Test_Init_1;

   procedure Test_Init_2 is
      C : Child;
      Y : RC_Acc := new Root'Class'(Root'Class (C));
   begin
      pragma Assert (Y.all not in Child); --@ASSERT:FAIL
   end Test_Init_2;

   procedure Test_Init_3 is
      C : Child;
      Z : R_Acc := new Root'(Root (C));
   begin
      pragma Assert (Z.all not in Root); --@ASSERT:FAIL
   end Test_Init_3;

   procedure Test_Init_4 is
      R : Root;
      C : Child;
      X : RC_Acc := new Root'Class'(Root'Class (R));
      Y : RC_Acc := new Root'Class'(Root'Class (C));
      Z : R_Acc := new Root'(Root (C));
   begin
      pragma Assert (X.all in Root);
      pragma Assert (Y.all in Child);
      pragma Assert (Z.all in Root);
   end Test_Init_4;

   procedure Test_Init_5 is
      C : Child;
      R : Root;
      X : RC_Acc := new Root'Class'(Root'Class (R));
   begin
      X.all := Root'Class (C); --@TAG_CHECK:FAIL
   end Test_Init_5;

begin
   null;
end Test_Tag;
