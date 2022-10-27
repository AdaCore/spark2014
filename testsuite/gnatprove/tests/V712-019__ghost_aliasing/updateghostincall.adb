pragma SPARK_Mode;
procedure Updateghostincall is
   type Ptr is access Integer;
   X : Ptr := new Integer'(42);
   procedure Update (Y : access Integer) with Ghost, Pre => True is
   begin
      Y.all := 1;
   end;
begin
   Update (X);
   pragma Assert (X.all = 1);
end Updateghostincall;
