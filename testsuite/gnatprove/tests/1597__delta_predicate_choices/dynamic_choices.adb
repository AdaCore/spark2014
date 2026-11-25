procedure Dynamic_Choices (Last : Integer) with
  SPARK_Mode,
  Pre => Last in 2 | 4
is
   subtype Even is Integer range 1 .. 4
     with Static_Predicate => Even in 2 | 4;
   subtype Narrow is Even range 2 .. Last;
   type Vector is array (1 .. 4) of Integer;
   X : constant Vector := [others => 0];
   Y : constant Vector := (X with delta Narrow => 9);
   Z : constant Vector := (X with delta Even range 2 .. Last => 8);
begin
   pragma Assert (Y (1) = 0 and Y (2) = 9 and Y (3) = 0); -- @ASSERT:PASS
   pragma Assert (Y (4) = (if Last = 4 then 9 else 0)); -- @ASSERT:PASS
   pragma Assert (Z (1) = 0 and Z (2) = 8 and Z (3) = 0); -- @ASSERT:PASS
   pragma Assert (Z (4) = (if Last = 4 then 8 else 0)); -- @ASSERT:PASS
end Dynamic_Choices;
