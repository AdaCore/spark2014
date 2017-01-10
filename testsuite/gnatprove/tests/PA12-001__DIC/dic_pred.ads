package DIC_Pred with SPARK_Mode is
   function Id (X : Integer) return Integer is (X);
   C : constant Integer := Id (0);
   type T is private with Default_Initial_Condition => Get (T) > 0;
   type S is private with Default_Initial_Condition => C >= 0;

   function Get (X : T) return Integer;

private
   type S is record
      F : Natural := C;
   end record;

   type T is record
      F : Natural := 0;
   end record with
     Dynamic_Predicate => Id (T.F) > 0;

   function Get (X : T) return Integer is (Id (X.F));

end DIC_Pred;
