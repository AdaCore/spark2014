procedure Addr is
   Arr : String := "hello";
begin
   for I in Arr'Range loop
      declare
         Val : Character with Import, Address => Arr(I)'Address; --@UNCHECKED_CONVERSION_VOLATILE:FAIL
      begin
         Val := Character'Pred (Val);
      end;
   end loop;
end Addr;
