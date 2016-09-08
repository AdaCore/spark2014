package body Types_With_Inv with SPARK_Mode is

   procedure Set_To_Zero (X : out T1) is
   begin
      X := 0;
   end Set_To_Zero;

   procedure Test (X : in out T2) is
   begin
      Set_To_Zero (X);  --@INVARIANT_CHECK:FAIL
      Set_To_Zero (T1 (X));  --@INVARIANT_CHECK:FAIL
   end Test;

   procedure Set_To_Zero (X : out R1) is
   begin
      X.F := 0;
   end Set_To_Zero;

   procedure Test (X : in out R2) is
   begin
      Set_To_Zero (X);  --@INVARIANT_CHECK:FAIL
      Set_To_Zero (R1 (X));  --@INVARIANT_CHECK:FAIL
   end Test;
end Types_With_Inv;
