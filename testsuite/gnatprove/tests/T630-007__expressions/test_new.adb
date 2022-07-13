procedure Test_New with SPARK_Mode is
   type Int_Acc is access Integer;

   function F (X : access constant Integer) return Boolean is
     (X /= null and then X.All = 12);
begin
   pragma Assert (F (Int_Acc'(new Integer'(12)))); --@RESOURCE_LEAK:FAIL
end Test_New;
