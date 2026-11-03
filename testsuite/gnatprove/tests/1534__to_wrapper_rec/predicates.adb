procedure Predicates (Minimum : Integer) with SPARK_Mode is
   type Container;
   type Access_T is access Container;

   type Container is record
      Data : Integer;
      Next : Access_T;
   end record
   with Dynamic_Predicate => Container.Data >= Minimum;

   procedure Check (N : in out Access_T) with Pre => N /= null is
      Wrapped : Access_T with Relaxed_Initialization;
   begin
      Wrapped := N;
      pragma Assert (Wrapped'Initialized); -- @ASSERT:PASS
      pragma Assert (Wrapped.all.Data >= Minimum); -- @ASSERT:PASS
      N := Wrapped; -- @INIT_BY_PROOF:PASS
   end Check;
begin
   null;
end Predicates;
