package body Parent.Child is

   procedure Swap is
      Tmp : Integer;
   begin
      Tmp := X + 1;
      X := Y;
      Y := Tmp;
   end;

end;
