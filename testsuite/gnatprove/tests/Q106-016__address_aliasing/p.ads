package P is

   X : Integer := 0;

   Y : Integer with Import; --@UNCHECKED_CONVERSION_ALIGN:PASS
   for Y'Address use X'Address;

   Z : Integer with Import, Address => X'Address; --@UNCHECKED_CONVERSION_ALIGN:PASS

end;
