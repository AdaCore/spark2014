procedure Forgetful_Assert (X : out Integer) with
  SPARK_Mode
is
begin
   X := 1;

   pragma Assert (X = 1);

   pragma Assert_And_Cut (X > 0);

   pragma Assert (X > 0);
   pragma Assert (X = 1);
end Forgetful_Assert;
