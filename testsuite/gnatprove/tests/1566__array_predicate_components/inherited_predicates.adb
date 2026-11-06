procedure Inherited_Predicates with SPARK_Mode is
   type Item is record
      F : Integer;
   end record;
   type Base_Record is record
      C : Item;
   end record with Dynamic_Predicate => True;
   type R is new Base_Record with Relaxed_Initialization;
   type Base_Array is array (1 .. 2) of Item with
     Dynamic_Predicate => True;
   type A is new Base_Array with Relaxed_Initialization;

   procedure Record_Component (Value : Item) with
     Global => null, Relaxed_Initialization => Value
   is
      X : R := (C => Value); -- @INIT_BY_PROOF:FAIL @PREDICATE_CHECK:PASS
   begin
      null;
   end Record_Component;

   -- Use ordinary destinations to isolate component checks from wrapper
   -- conversions.
   procedure Array_Component (Value : Item) with
     Global => null, Relaxed_Initialization => Value
   is
      X : Base_Array := Base_Array (A'(others => Value)); -- @INIT_BY_PROOF:FAIL @PREDICATE_CHECK:PASS
   begin
      null;
   end Array_Component;

   procedure Initialized_Array (Value : Item) with
     Global => null, Relaxed_Initialization => Value,
     Pre => Value'Initialized
   is
      X : Base_Array := Base_Array (A'(others => Value)); -- @INIT_BY_PROOF:PASS @PREDICATE_CHECK:PASS
   begin
      pragma Assert (X (1).F = Value.F); -- @ASSERT:PASS
   end Initialized_Array;
begin
   null;
end Inherited_Predicates;
