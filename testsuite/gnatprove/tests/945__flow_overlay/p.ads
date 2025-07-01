package P is
   X : constant Integer := 0;
   Y : constant Integer with Import, Address => X'Address;
   Z : constant Boolean := Y'Valid;
end;
