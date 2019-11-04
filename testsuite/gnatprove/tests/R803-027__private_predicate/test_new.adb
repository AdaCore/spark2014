with Pred_Vis; use Pred_Vis;
procedure Test_New (X : Grand_Grand_Child; Y : Grand_Grand_Child_2; Z : Grand_Grand_Child_3) with SPARK_Mode is
   pragma Assert (X.F1 > 0);
   pragma Assert (X.G1 > 10); --@ASSERT:FAIL
   pragma Assert (X.G2 > 15);
   pragma Assert (X.F1 < 100); --@ASSERT:FAIL
   pragma Assert (Y.F1 > 0);
   pragma Assert (Y.G1 > 10); --@ASSERT:FAIL
   pragma Assert (Y.G2 > 15); --@ASSERT:FAIL
   pragma Assert (Y.F1 < 100); --@ASSERT:FAIL
   pragma Assert (Z.F1 > 0);
   pragma Assert (Z.G1 > 10); --@ASSERT:FAIL
   pragma Assert (Z.G2 > 15);
   pragma Assert (Z.F2 > 0 and Z.F1 < 100);
begin
   null;
end Test_New;
