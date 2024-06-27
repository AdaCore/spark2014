with P; use P;

--  Test correct handling of globally assumed invariants on private subprograms.
--  The invariant of S1 can be assumed on value as it is local to Nested while
--  the invariant of S2 might be broken.
--  The definitions of Incr and Decr should be available and enough to show that
--  Id is the identity.

procedure Test (X : S2) with SPARK_Mode is
begin
   pragma Assert (X = Id (X));     --@ASSERT:PASS
   pragma Assert (Value_Is_OK_1);  --@ASSERT:PASS
   pragma Assert (Value_Is_OK_2);  --@ASSERT:FAIL
end Test;
