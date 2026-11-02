procedure Example with SPARK_Mode is
   X : Integer := 0;

   procedure P with Pre => X = 0 is
      Y : Integer := 1 with Address => X'Address;
      package Nested is
      end Nested;
      package body Nested is
      begin
         pragma Assert (X = 0); -- ASSERT:FAIL
      end Nested;
   begin
      null;
   end P;
begin
   P;
end Example;
