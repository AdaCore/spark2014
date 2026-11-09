with Empty_Generic;

procedure Instantiation with SPARK_Mode is
   X : Integer := 0;
   Y : Integer := 1 with Address => X'Address;
   package Nested is new Empty_Generic;
begin
   null;
end Instantiation;
