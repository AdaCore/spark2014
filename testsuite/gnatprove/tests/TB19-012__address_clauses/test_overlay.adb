procedure Test_Overlay (C : Integer; D : in out Integer) with SPARK_Mode is
   X : constant Integer := 15;
   Y : Integer with Address => X'Address; --rejected
   Z : Integer with Address => C'Address; --rejected
   W : Integer with Address => D'Address; --ok
begin
   null;
end Test_Overlay;
