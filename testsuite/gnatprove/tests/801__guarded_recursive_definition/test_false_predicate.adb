procedure Test_False_Predicate with SPARK_Mode is

   function Id (X : Boolean) return Boolean is (X);

   subtype Nothing is Boolean with Predicate => Id (False);
   function Bad2 (X : Nothing) return Boolean
     with Subprogram_Variant => (Increases => X);
   function Bad (X : Nothing) return Boolean is (Bad2 (X))
     with Subprogram_Variant => (Increases => X);
   function Bad2 (X : Nothing) return Boolean is (not Bad (X));

   procedure Test is
   begin
      pragma Assert (if Id (False) then Bad (True));
      pragma Assert (False); --@ASSERT:FAIL
   end Test;
begin
   null;
end Test_False_Predicate;
