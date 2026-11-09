procedure Package_Before (X : in out Integer) with
  SPARK_Mode,
  Pre => X = 0
is
   package Nested is
      C : constant Integer := 0;
   end Nested;
   Y : Integer := 1 with Address => X'Address;
begin
   null;
end Package_Before;
