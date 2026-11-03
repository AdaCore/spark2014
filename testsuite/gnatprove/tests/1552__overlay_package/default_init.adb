procedure Default_Init with SPARK_Mode is
   type Rec is record
      F : Integer := 1;
   end record;
   X : Rec := (F => 0);

   procedure P with Pre => X.F = 0 is
      Y : Rec with Address => X'Address;
      package Nested is
      end Nested;
      package body Nested is
      begin
         pragma Assert (X.F = 0); -- ASSERT:FAIL
      end Nested;
   begin
      null;
   end P;
begin
   P;
end Default_Init;
