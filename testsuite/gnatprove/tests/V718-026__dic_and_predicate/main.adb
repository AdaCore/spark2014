procedure Main with SPARK_Mode is

   --  This test checks that DICs and predicates are checked in the expected
   --  order when they apply to the same type.

   function P (X : Integer) return Boolean with
     Import,
     Global => null,
     Annotate => (GNATprove, Always_Return);
   function Q (X : Integer) return Boolean with
     Import,
     Global => null,
     Annotate => (GNATprove, Always_Return);
   function R (X : Integer) return Boolean with
     Import,
     Global => null,
     Annotate => (GNATprove, Always_Return);

   --  The predicate is on the ancestor, check it before

   package P1 is

      type T1 is private with  -- @PREDICATE_CHECK:FAIL  -- @DEFAULT_INITIAL_CONDITION:PASS
        Default_Initial_Condition => P (Get (T1));

      function Get (X : T1) return Integer;

   private

      type T is record
         F : Integer := 0;
      end record with
        Predicate => P (F);

      type T1 is new T;

      function Get (X : T1) return Integer is (X.F);

   end P1;

   --  The DIC is on the ancestor, check it before

   package P2 is

      type T1 is private with  -- @DEFAULT_INITIAL_CONDITION:FAIL
        Default_Initial_Condition => P (Get (T1));

      function Get (X : T1) return Integer;

      type T2 is private;  -- @PREDICATE_CHECK:PASS

   private

      type T1 is record
         F : Integer := 0;
      end record;

      function Get (X : T1) return Integer is (X.F);

      type T2 is new T1 with
        Predicate => P (F);

   end P2;

   --  The predicate and the DIC are at the same place, check the predicate first

   package P3 is

      type T1 is private with  -- @PREDICATE_CHECK:FAIL  -- @DEFAULT_INITIAL_CONDITION:PASS
        Default_Initial_Condition => P (Get (T1));

      function Get (X : T1) return Integer;

   private

      type T1 is record
         F : Integer := 0;
      end record with
        Predicate => P (F);

      function Get (X : T1) return Integer is (X.F);

   end P3;

   --  The predicate is checked between the 2 DICs

   package P4 is

      type T1 is private with  -- @DEFAULT_INITIAL_CONDITION:FAIL
        Default_Initial_Condition => P (Get (T1));

      function Get (X : T1) return Integer;

      type T2 is private with  -- @DEFAULT_INITIAL_CONDITION:PASS  -- @PREDICATE_CHECK:FAIL
        Default_Initial_Condition => Q (Get (T2));

      function Get (X : T2) return Integer;

   private

      type T1 is record
         F : Integer := 0;
      end record;

      function Get (X : T1) return Integer is (X.F);

      type T2 is new T1 with
        Predicate => P (F) and Q (F);

      function Get (X : T2) return Integer is (X.F);

   end P4;

   --  The predicate of T2 is checked between the 2 DICs, the predicate of T3
   --  is checked afterward.

   package P5 is

      type T1 is private with  -- @DEFAULT_INITIAL_CONDITION:FAIL
        Default_Initial_Condition => P (Get (T1));

      function Get (X : T1) return Integer;

      type T2 is private with  -- @DEFAULT_INITIAL_CONDITION:PASS  -- @PREDICATE_CHECK:FAIL
        Default_Initial_Condition => Q (Get (T2));

      function Get (X : T2) return Integer;

      type T3 is private with  -- @DEFAULT_INITIAL_CONDITION:PASS  -- @PREDICATE_CHECK:FAIL
        Default_Initial_Condition => R (Get (T3));

      function Get (X : T3) return Integer;

   private

      type T1 is record
         F : Integer := 0;
      end record;

      function Get (X : T1) return Integer is (X.F);

      type T2 is new T1 with
        Predicate => P (F) and Q (F);

      function Get (X : T2) return Integer is (X.F);

      type T3 is new T2 with
        Predicate => P (F) and Q (F) and R (F);

      function Get (X : T3) return Integer is (X.F);

   end P5;

   --  The DIC is checked at use. Check the predicate assuming the DIC holds.

   package P6 is

      type T1 (D : Integer) is private with  -- @PREDICATE_CHECK:PASS  -- @DEFAULT_INITIAL_CONDITION:NONE
        Default_Initial_Condition => P (D);

   private

      type T1 (D : Integer) is record
         F : Integer := 0;
      end record with
        Predicate => P (D);

      X : T1 (D => 0); -- @DEFAULT_INITIAL_CONDITION:FAIL

   end P6;

   --  The DIC on the ancestor is checked at use. Check the predicate assuming the DIC holds.

   package P7 is

      type T1 (D : Integer) is tagged private with  -- @DEFAULT_INITIAL_CONDITION:NONE
        Default_Initial_Condition => P (D);

      type T2 is new T1 with private;  -- @PREDICATE_CHECK:PASS

   private

      type T1 (D : Integer) is tagged record
         F : Integer := 0;
      end record;

      type T2 is new T1 with null record with
        Predicate => P (T2.D);

      X : T2 (D => 0); -- @DEFAULT_INITIAL_CONDITION:FAIL

   end P7;

   --  The DIC on T1 is checked at use. Check all predicates, inherited or not,
   --  assuming the DIC holds.

   package P8 is
      type T (D : Integer) is tagged record  -- @PREDICATE_CHECK:NONE
         F : Integer := 0;
      end record with
        Predicate => (P (D));

      type T1 is new T with private with  -- @PREDICATE_CHECK:PASS  -- @DEFAULT_INITIAL_CONDITION:NONE
        Default_Initial_Condition => P (T1.D);

   private

      type T1 is new T with null record;

      X : T1 (D => 0); -- @DEFAULT_INITIAL_CONDITION:FAIL
   end P8;

   --  The predicate is checked after the DIC of T1 which is checked at use and
   --  before the DIC of T2.

   package P9 is

      type T1 (D : Integer) is tagged private with  -- @DEFAULT_INITIAL_CONDITION:NONE
        Default_Initial_Condition => P (D);

      type T2 is new T1 with private with  -- @DEFAULT_INITIAL_CONDITION:PASS  -- @PREDICATE_CHECK:FAIL
        Default_Initial_Condition => Q (Get (T2));

      function Get (X : T2'Class) return Integer;

   private

      type T1 (D : Integer) is tagged record
         F : Integer := 0;
      end record;

      type T2 is new T1 with null record with
        Predicate => P (D) and Q (F);

      function Get (X : T2'Class) return Integer is (X.F);

      X : T2 (D => 0); -- @DEFAULT_INITIAL_CONDITION:FAIL

   end P9;

   --  The predicate is checked after the DIC of T1 and after the DIC of T2
   --  which is checked at use.

   package P10 is

      type T1 (D : Integer) is tagged private with  -- @DEFAULT_INITIAL_CONDITION:FAIL
        Default_Initial_Condition => P (Get (T1));

      function Get (X : T1'Class) return Integer;

      type T2 is new T1 with private with  -- @DEFAULT_INITIAL_CONDITION:NONE  -- @PREDICATE_CHECK:PASS
        Default_Initial_Condition => Q (T2.D);

   private

      type T1 (D : Integer) is tagged record
         F : Integer := 0;
      end record;

      function Get (X : T1'Class) return Integer is (X.F);

      type T2 is new T1 with null record with
        Predicate => P (F) and Q (D);

      X : T2 (D => 0); -- @DEFAULT_INITIAL_CONDITION:FAIL

   end P10;

   --  The predicate is checked after the DICs of T1 and T2 which are checked
   --  at use.

   package P11 is

      type T1 (D : Integer) is tagged private with  -- @DEFAULT_INITIAL_CONDITION:NONE
        Default_Initial_Condition => P (D);

      type T2 is new T1 with private with  -- @DEFAULT_INITIAL_CONDITION:NONE  -- @PREDICATE_CHECK:PASS
        Default_Initial_Condition => Q (T2.D);

   private

      type T1 (D : Integer) is tagged record
         F : Integer := 0;
      end record;

      type T2 is new T1 with null record with
        Predicate => P (D) and Q (D);

      X : T2 (D => 0); -- @DEFAULT_INITIAL_CONDITION:FAIL

   end P11;

   --  The predicate is checked after the DICs of T1, T2 and T3 which are checked
   --  at use.

   package P12 is

      type T1 (D : Integer) is tagged private with  -- @DEFAULT_INITIAL_CONDITION:NONE
        Default_Initial_Condition => P (D);

      type T2 is new T1 with private with  -- @DEFAULT_INITIAL_CONDITION:NONE  -- @PREDICATE_CHECK:PASS
        Default_Initial_Condition => Q (T2.D);

      type T3 is new T2 with private with  -- @DEFAULT_INITIAL_CONDITION:NONE  -- @PREDICATE_CHECK:PASS
        Default_Initial_Condition => R (T3.D);

   private

      type T1 (D : Integer) is tagged  record
         F : Integer := 0;
      end record;

      type T2 is new T1 with null record with
        Predicate => P (T2.D) and Q (T2.D);

      type T3 is new T2 with null record with
        Predicate => P (T3.D) and Q (T3.D) and R (T3.D);

      X : T3 (D => 0); -- @DEFAULT_INITIAL_CONDITION:FAIL

   end P12;


begin
   null;
end Main;
