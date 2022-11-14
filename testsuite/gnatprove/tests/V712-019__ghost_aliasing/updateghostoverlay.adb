pragma SPARK_Mode;
procedure Updateghostoverlay is
   type Ptr is access Integer;
   X : Ptr := new Integer'(42);
begin
   declare
      Y : Integer := 0 with Ghost, Address => X.all'Address;
   begin
      Y := 1;
   end;
   pragma Assert (X.all = 1);
end Updateghostoverlay;
