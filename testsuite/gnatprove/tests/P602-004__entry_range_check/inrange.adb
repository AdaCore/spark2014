package body InRange is

   protected body PT is
      entry Add_Out (I : in out int20; J : int10) when True
      is
      begin
         I := I + J;
      end Add_Out;
   end PT;

   procedure Do_It
   is
      X, Y : int10 := 10;
   begin
      PO.Add_Out (X, Y); --@RANGE_CHECK:FAIL
      pragma Assert (X <= 10);
   end Do_It;

end InRange;
