procedure Array_Assignment (N : Positive) with SPARK_Mode is
   type A is array (Positive range <>) of Integer;
   subtype S is A with
     Dynamic_Predicate => (for all E of S => E >= 0);

   X : S (1 .. N) with Relaxed_Initialization;
begin
   X := (others => 0); -- @PREDICATE_CHECK:PASS @LENGTH_CHECK:PASS @INIT_BY_PROOF:NONE
   pragma Assert (X'Initialized); -- @ASSERT:PASS
end Array_Assignment;
