with Hidden_Private_Part; use Hidden_Private_Part;
procedure Test_Hidden_Private (X : T; Y1 : T_P1; Y2 : T_P2) with SPARK_Mode is
begin
   --  The full view of T is hidden
   pragma Assert (X = X); -- @ASSERT:FAIL

   --  The definition of Return_0 is hidden
   pragma Assert (Return_0 = 0); -- @ASSERT:FAIL

   --  The completion of Zero is hidden
   pragma Assert (Zero = Id (0)); -- @ASSERT:FAIL

   --  The predicate of T_P2 is hidden
   pragma Assert (Y2.D /= 0); -- @ASSERT:FAIL

   --  The definitions of Return_1 and Return_2 are visible
   pragma Assert (Return_1 = 1); -- @ASSERT:PASS
   pragma Assert (Return_2 = 2); -- @ASSERT:PASS

   --  The completion of One is visible
   pragma Assert (One = Id (1)); -- @ASSERT:PASS

   --  The predicate of T_P1 is visible
   pragma Assert (Y1.D /= 0); -- @ASSERT:PASS
end Test_Hidden_Private;
