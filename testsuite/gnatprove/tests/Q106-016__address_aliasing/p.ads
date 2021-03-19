package P is

   X : Integer := 0;

   Y : Integer with Import;
   for Y'Address use X'Address;

   Z : Integer with Import, Address => X'Address;

end;
