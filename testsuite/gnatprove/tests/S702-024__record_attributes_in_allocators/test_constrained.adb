procedure Test_Constrained with SPARK_Mode is
   type R (B : Boolean := True) is record
      X : Integer := 0;
   end record;
   subtype R_F is R (False);

   type R_A is array (Positive range 1 .. 10) of R;

   type R_Acc is access R;
   type R_A_Acc is access R_A;

   procedure Test_1 is
      Y : R_Acc := new R;
   begin
      pragma Assert (not Y.all'Constrained); --@ASSERT:FAIL
   end Test_1;

   procedure Test_2 is
      Y : R_Acc := new R;
   begin
      Y.all := (B => False, others => 0); --@DISCRIMINANT_CHECK:FAIL
   end Test_2;

   procedure Test_3 is
      Y : R_Acc := new R'(B => False, others => <>);
   begin
      pragma Assert (not Y.all'Constrained); --@ASSERT:FAIL
   end Test_3;

   procedure Test_4 is
      Y : R_Acc := new R'(B => False, others => <>);
   begin
      Y.all := (B => True, others => 0); --@DISCRIMINANT_CHECK:FAIL
   end Test_4;

   procedure Test_5 is
      Y : R_Acc := new R_F;
   begin
      Y.all := (B => True, others => 0); --@DISCRIMINANT_CHECK:FAIL
   end Test_5;

   procedure Test_6 is
      X : constant R_A_Acc := new R_A;
   begin
      pragma Assert (X (1)'Constrained); --@ASSERT:FAIL
   end Test_6;

   X : constant R_A_Acc := new R_A;
   V : R := (B => True, others => 0);
begin
   V := (B => False, others => 0);
   pragma Assert (not X (1)'Constrained);
   X (1) := V;
end Test_Constrained;
