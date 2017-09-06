procedure Variable_Address is
   X : Integer := 1;
   Y : Integer := 0 with Address => X'Address;
begin
   pragma Assert (X = 1);
end Variable_Address;
