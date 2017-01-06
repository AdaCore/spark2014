package P is

   X : Integer := 0;

   Y : Integer;
   for Y'Address use X'Address;

   Z : Integer with Address => X'Address;

end;
