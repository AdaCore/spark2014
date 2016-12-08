package DIC_Pred with SPARK_Mode is
   type T is private with Default_Initial_Condition => Get (T) > 0;
   type S is private with Default_Initial_Condition => False;

   function Get (X : T) return Integer;

private

   function Id (X : Integer) return Integer is (X);
   type S is null record;

   type T is record
      F : Natural := 0;
   end record with
     Dynamic_Predicate => Id (T.F) > 0;

   function Get (X : T) return Integer is (Id (X.F));

end DIC_Pred;
