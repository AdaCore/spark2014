with Empty_Generic;

procedure Instantiation_Before with SPARK_Mode is
   X : Integer := 0;
   package Nested is new Empty_Generic;
   Y : Integer := 1 with Address => X'Address;
begin
   null;
end Instantiation_Before;
