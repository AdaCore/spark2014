pragma Extensions_Allowed (All_Extensions);

--  Check that checks are introduced for Loop_Entry references even if they
--  occur in a dead context.

procedure Test with SPARK_Mode
is
   pragma Unevaluated_Use_Of_Old (Allow);
   function Id (X : Integer) return Integer is (X);
   X : constant Integer := Id (0);
begin
   for I in 1 .. 100 loop
      pragma Loop_Invariant (if I < Id (1) then Integer'(1 / X)'Loop_Entry = 1); -- @DIVISION_CHECK:FAIL
   end loop;
end;
