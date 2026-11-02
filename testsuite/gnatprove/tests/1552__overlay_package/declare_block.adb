procedure Declare_Block with SPARK_Mode is
begin
   declare
      package Nested is
         X : Integer := 0;
      end Nested;
      Y : Integer := 1;
      for Y'Address use Nested.X'Address;
      package body Nested is
      begin
         pragma Assert (X = 0); -- ASSERT:FAIL
      end Nested;
   begin
      null;
   end;
end Declare_Block;
