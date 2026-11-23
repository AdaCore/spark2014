procedure Aggregate_Choices with SPARK_Mode is
   subtype Even is Integer range 1 .. 4
     with Static_Predicate => Even in 2 | 4;
   subtype Two is Even range 2 .. 2;
   type Vector is array (1 .. 4) of Integer;
   A : constant Vector := [Even range 2 .. 2 => 8, others => 0];
   B : constant Vector := [Two => 8, others => 0];
   C : constant Vector := [Even range 2 .. 4 => 8, others => 0];
begin
   pragma Assert (A = [0, 8, 0, 0]); -- @ASSERT:PASS
   pragma Assert (B = [0, 8, 0, 0]); -- @ASSERT:PASS
   pragma Assert (C = [0, 8, 0, 8]); -- @ASSERT:PASS
end Aggregate_Choices;
