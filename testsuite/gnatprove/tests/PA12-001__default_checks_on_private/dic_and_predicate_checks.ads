package DIC_And_Predicate_Checks with SPARK_Mode is
   type R is record
      F : Integer;
      G : Integer := 0;
   end record;

   function Is_Valid (X : R) return Boolean is (X.F > 0);

   package Nested_1 is
      type T is private with Default_Initial_Condition => Is_Valid (T);  -- Old: DIC might fail

      function Is_Valid (X : T) return Boolean;
   private
      type T is new R with Predicate => Is_Valid (R (T));  -- New: predicate might fail on default value

      function Is_Valid (X : T) return Boolean is (Is_Valid (R (X)));
   end Nested_1;

   package Nested_2 is
      type R is record
         F : Integer;
      end record with Predicate => F > 0; -- New: predicate might fail on default value

      type T is private with Default_Initial_Condition => Is_Valid (T);  -- Old: DIC might fail

      function Is_Valid (X : T) return Boolean;
   private
      type T is new R;
      function Is_Valid (X : T) return Boolean is (X.F > 0);
   end Nested_2;

   package Nested_3 is
      type P is private with Default_Initial_Condition => Is_Valid (P); -- New: DIC might fail

      function Is_Valid (X : P) return Boolean;
   private
      type P is new R;
      function Is_Valid (X : P) return Boolean is (Is_Valid (R (X)));
   end Nested_3;

   type Nested_3_T is new Nested_3.P with  -- Old: predicate might fail on default value
     Predicate => Nested_3.Is_Valid (Nested_3.P (Nested_3_T));

   package Nested_4 is
      type P is private with Default_Initial_Condition => False;
      type T is private; --  No DIC check
   private
      pragma SPARK_Mode (Off);
      type P is new R;
      type T is new P;
   end Nested_4;

   X1 : Nested_1.T;
   X2 : Nested_2.T;
   X3 : Nested_3_T;
   X4 : Nested_4.T;
end DIC_And_Predicate_Checks;
