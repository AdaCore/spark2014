procedure Predicate_Choices with SPARK_Mode is
   subtype Even is Integer range 1 .. 4
     with Static_Predicate => Even in 2 | 4;
   subtype Middle is Integer range 2 .. 3;
   type Vector is array (1 .. 4) of Integer;
   X : constant Vector := [others => 0];
   Y : constant Vector := (X with delta Even => 9);
   Z : constant Vector := (X with delta Even range 2 .. 2 => 8);
   S : constant Vector := (X with delta Even range 2 .. 4 => 8);
   W : constant Vector := (X with delta Even => 9, 4 => 7);
   R : constant Vector := (X with delta Middle => 6);
begin
   pragma Assert (Y = [0, 9, 0, 9]); -- @ASSERT:PASS
   pragma Assert (Z = [0, 8, 0, 0]); -- @ASSERT:PASS
   pragma Assert (S = [0, 8, 0, 8]); -- @ASSERT:PASS
   pragma Assert (W = [0, 9, 0, 7]); -- @ASSERT:PASS
   pragma Assert (R = [0, 6, 6, 0]); -- @ASSERT:PASS
end Predicate_Choices;
