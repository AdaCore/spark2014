pragma SPARK_Mode;
procedure Updateghost is
   type Ptr is access Integer;
   X : Ptr := new Integer'(42);
begin
   declare
      Y : access Integer := X with Ghost;
   begin
      Y.all := 1;
   end;
   pragma Assert (X.all = 1);
end Updateghost;
