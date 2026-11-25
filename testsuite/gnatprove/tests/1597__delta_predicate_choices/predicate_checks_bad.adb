procedure Predicate_Checks_Bad (First : Integer) with
  SPARK_Mode,
  Pre => First = 1
is
   subtype Selected is Integer range 0 .. 4
     with Dynamic_Predicate => Selected mod 2 = 0 and Selected /= 4;
   type Vector is array (Integer range <>) of Integer;
   X : constant Vector (First .. 4) := [others => 0];
   Y : constant Vector := (X with delta Selected => 9); -- @INDEX_CHECK:FAIL
begin
   pragma Assert (Y (2) = 9); -- @ASSERT:PASS
end Predicate_Checks_Bad;
