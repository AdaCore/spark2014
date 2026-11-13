procedure Explicit_Array_Elements with SPARK_Mode is
   type Item is record
      F : Integer;
   end record;
   type A is array (1 .. 2) of Item with
     Dynamic_Predicate => True;

   procedure Build (Value : Item) with
     Global => null, Relaxed_Initialization => Value
   is
      X : A := (others => Value); -- @INIT_BY_PROOF:FAIL @PREDICATE_CHECK:PASS
   begin
      null;
   end Build;
begin
   null;
end Explicit_Array_Elements;
