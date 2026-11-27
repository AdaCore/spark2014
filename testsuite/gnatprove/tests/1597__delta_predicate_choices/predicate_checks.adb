procedure Predicate_Checks with SPARK_Mode is
   subtype Selected is Integer range 0 .. 5
     with Dynamic_Predicate => Selected mod 2 = 0 and Selected /= 0;
   subtype None is Integer range 0 .. 5
     with Dynamic_Predicate => None < 0;
   type Vector is array (1 .. 4) of Integer;
   X : constant Vector := [others => 0];
   Y : constant Vector := (X with delta Selected => 9); -- @INDEX_CHECK:PASS
   Z : constant Vector := (X with delta None => 9); -- @INDEX_CHECK:PASS
   V : constant Vector := (X with delta Selected range 2 .. 2 => 7); -- @INDEX_CHECK:PASS
   U : constant Vector := X'Update (Selected range 2 .. 4 => 9); -- @INDEX_CHECK:PASS
begin
   pragma Assert (Y = [0, 9, 0, 9]); -- @ASSERT:PASS
   pragma Assert (Z = X); -- @ASSERT:PASS
   pragma Assert (V = [0, 7, 0, 0]); -- @ASSERT:PASS
   pragma Assert (U = Y); -- @ASSERT:PASS
   --  An empty choice must not make subsequent checks vacuous.
   pragma Assert (False); -- @ASSERT:FAIL
end Predicate_Checks;
