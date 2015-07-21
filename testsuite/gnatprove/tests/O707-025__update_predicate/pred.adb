procedure Pred
  with SPARK_Mode
is
   type T is record
      C : Integer;
      D : Integer;
   end record with Dynamic_Predicate => T.D = T.C + 2;
   X : T := (C => 2, D => 4);  --  @PREDICATE_CHECK:PASS
begin
   X := X'Update (C => 4, D => 6);  --  @PREDICATE_CHECK:PASS
end Pred;
