package body Records
is
   pragma Warnings (Off, "* has no effect");

   procedure Aggregate_In_Quantifier
     with Depends => null,
          Pre     => (for all N in Unsigned_Byte => F_Of_Pair (Apir1'(0, N)))
   is
   begin
      pragma Assert (Apir1'(5, 6) = (A => 1, B => 1));  --  @ASSERT:FAIL
      null;
   end Aggregate_In_Quantifier;

   pragma Warnings (On, "* has no effect");
end Records;
