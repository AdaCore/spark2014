procedure Array_Conversion with SPARK_Mode is
   type Base_Array is array (1 .. 2) of Integer with
     Dynamic_Predicate => True;
   type A is new Base_Array with Relaxed_Initialization;

   X : A := (others => 0); -- @PREDICATE_CHECK:PASS
begin
   pragma Assert (X (1) = 0); -- @ASSERT:PASS
end Array_Conversion;
