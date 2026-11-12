procedure Predicates with SPARK_Mode is
   type Base_Record is record
      F : Integer;
   end record with Dynamic_Predicate => True;
   type R is new Base_Record with Relaxed_Initialization;

   procedure Boxed_Record with Global => null is
      X : R := (F => <>); -- @INIT_BY_PROOF:FAIL @PREDICATE_CHECK:PASS
   begin
      null;
   end Boxed_Record;

   procedure Initialized_Record with Global => null is
      X : R := (F => 0); -- @PREDICATE_CHECK:PASS
   begin
      pragma Assert (X.F = 0);
   end Initialized_Record;

   type Base_Array is array (1 .. 2) of Integer with
     Dynamic_Predicate => True;
   type A is new Base_Array with Relaxed_Initialization;

   -- Use ordinary destinations to isolate aggregate checks from wrapper
   -- conversions.
   procedure Boxed_Array with Global => null is
      X : Base_Array := Base_Array (A'(others => <>)); -- @INIT_BY_PROOF:FAIL @PREDICATE_CHECK:PASS
   begin
      null;
   end Boxed_Array;

   type Inner is record
      F : Integer;
   end record;
   type Base_Holder is record
      C : Inner;
   end record with Dynamic_Predicate => True;
   type Holder is new Base_Holder with Relaxed_Initialization;

   procedure Composite_Box with Global => null is
      X : Holder := (C => <>); -- @INIT_BY_PROOF:FAIL @PREDICATE_CHECK:PASS
   begin
      null;
   end Composite_Box;

   type Base_Composite_Array is array (1 .. 2) of Inner with
     Dynamic_Predicate => True;
   type Composite_Array is new Base_Composite_Array with Relaxed_Initialization;

   procedure Composite_Array_Box with Global => null is
      X : Base_Composite_Array := Base_Composite_Array (Composite_Array'(others => <>)); -- @INIT_BY_PROOF:FAIL @PREDICATE_CHECK:PASS
   begin
      null;
   end Composite_Array_Box;

   type Defaulted is record
      F : Integer := 42;
   end record;
   type Base_Defaulted_Holder is record
      C : Defaulted;
   end record with Dynamic_Predicate => True;
   type Defaulted_Holder is new Base_Defaulted_Holder
     with Relaxed_Initialization;

   procedure Initialized_Composite_Box (Result : out Integer) with
     Global => null
   is
      X : Defaulted_Holder := (C => <>); -- @INIT_BY_PROOF:NONE @PREDICATE_CHECK:PASS
   begin
      Result := X.C.F; -- @INIT_BY_PROOF:PASS
      pragma Assert (Result = 42);
   end Initialized_Composite_Box;

   type Partial_Record is record
      F : Integer;
   end record with Relaxed_Initialization, Ghost_Predicate => True;

   procedure Partial_Box with Global => null is
      X : Partial_Record := (F => <>); -- @PREDICATE_CHECK:PASS
   begin
      pragma Assert (X'Initialized); -- @ASSERT:FAIL
   end Partial_Box;

   type Predicated_Inner is record
      F : Integer;
   end record with Dynamic_Predicate => True;
   type Relaxed_Holder is record
      C : Predicated_Inner;
   end record with Relaxed_Initialization;

   procedure Nested_Predicate with Global => null is
      X : Relaxed_Holder := (C => (F => <>)); -- @INIT_BY_PROOF:FAIL @PREDICATE_CHECK:PASS
   begin
      null;
   end Nested_Predicate;
begin
   null;
end Predicates;
