procedure Addr is
   Arr : String := "hello";
begin
   for I in Arr'Range loop
      declare
         Val : Character with Address => Arr(I)'Address;
      begin
         Val := Character'Pred (Val);
      end;
   end loop;
end Addr;
