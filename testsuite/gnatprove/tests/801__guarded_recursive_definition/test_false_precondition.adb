procedure Test_False_Precondition with SPARK_Mode is
   function Id (X : Boolean) return Boolean is (X);

   function Bad2 (X : Boolean) return Boolean
     with Pre => Id (False), Subprogram_Variant => (Increases => X);
   function Bad (X : Boolean) return Boolean is (Bad2 (X))
     with Pre => Id (False), Subprogram_Variant => (Increases => X);
   function Bad2 (X : Boolean) return Boolean is (not Bad (X));

   procedure Test is
   begin
      pragma Assert (if Id (False) then Bad (True));
      pragma Assert (False); --@ASSERT:FAIL
   end Test;
begin
   null;
end Test_False_Precondition;
