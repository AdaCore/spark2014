procedure Null_Exclusion with SPARK_Mode is
   type Int_Acc is not null access Integer;

   function Id (X : access constant Integer) return access constant Integer is
      (X); --@NULL_EXCLUSION:NONE

   type With_Pred is access Float with
     Predicate => (if With_Pred /= null then With_Pred.all >= 0.0);

   X : With_Pred;

   procedure Do_Nothing (Y : not null access Float) is
   begin
      Y.all := -13.0;
      pragma Assert (X /= Y);--@PREDICATE_CHECK:NONE
   end Do_Nothing;
begin
   null;
end Null_Exclusion;
