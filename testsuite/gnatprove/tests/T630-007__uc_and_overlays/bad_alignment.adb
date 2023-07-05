procedure Bad_Alignment with SPARK_Mode is
   X : Integer := 16 with Alignment => 2;
   Y : Integer with Import, Alignment => 4, Address => X'Address; --@UNCHECKED_CONVERSION_ALIGN:FAIL
   Z : Integer with Import, Address => X'Address; --@UNCHECKED_CONVERSION_ALIGN:FAIL
   W : Integer with Import, Alignment => 2, Address => Z'Address; --@UNCHECKED_CONVERSION_ALIGN:FAIL

   procedure P (X : Integer) is
      Z : constant Integer with Alignment => 2, Import, Address => X'Address; --@UNCHECKED_CONVERSION_ALIGN:FAIL
   begin
      null;
   end P;
begin
   null;
end Bad_Alignment;
