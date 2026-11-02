procedure Between_Parts with SPARK_Mode is
   package Nested is
      X : Integer := 0;
   end Nested;
   Y : Integer := 1 with Address => Nested.X'Address;
   package body Nested is
   begin
      pragma Assert (X = 0); -- ASSERT:FAIL
   end Nested;
begin
   null;
end Between_Parts;
