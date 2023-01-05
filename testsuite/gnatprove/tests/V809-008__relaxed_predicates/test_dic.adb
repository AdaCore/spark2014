procedure Test_DIC with SPARK_Mode is

   --  Test case where a type with Relaxed_Initialization has a DIC and
   --  possibly a predicate.

   package Nested is
      --  This is fine, F can be called in the DIC without an initialization
      --  check.
      type T1 is private with
        Relaxed_Initialization,
        Default_Initial_Condition => F (T1);

      function F (X : T1) return Boolean;

      --  This is fine, F can be called in the DIC without an initialization
      --  check and the predicate holds.
      type T2 is private with
        Relaxed_Initialization,
        Default_Initial_Condition => F (T2);

      function F (X : T2) return Boolean;

      --  The DIC does not hold
      type T3 is private with --@DEFAULT_INITIAL_CONDITION:FAIL
        Relaxed_Initialization,
        Default_Initial_Condition => F (T3);

      function F (X : T3) return Boolean;

      --  Neither the predicate nor the DIC hold, but the predicate is checked
      --  first.
      type T4 is private with --@PREDICATE_CHECK:FAIL
        Relaxed_Initialization,
        Default_Initial_Condition => F (T4);

      function F (X : T4) return Boolean;
   private
      type T1 is record
         F : Boolean := True;
         G : Boolean;
      end record;

      function F (X : T1) return Boolean is
        (X.F);

      type T2 is record
         F : Boolean := True;
         G : Boolean;
      end record with
        Predicate => F;

      function F (X : T2) return Boolean is
        (X.F);

      type T3 is record
         F : Boolean;
         G : Boolean;
      end record;

      function F (X : T3) return Boolean is
        (X.F);

      type T4 is record
         F : Boolean;
         G : Boolean;
      end record with
        Predicate => F;

      function F (X : T4) return Boolean is
        (X.F);
   end Nested;

begin
   null;
end Test_DIC;
