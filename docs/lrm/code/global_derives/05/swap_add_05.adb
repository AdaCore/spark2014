package body Swap_Add_05
is
   procedure Swap
   is
      Temporary: Integer;
   begin
      Temporary := X;
      X         := Y;
      Y         := Temporary;
   end Swap;

   function Add return Integer
   is
   begin
      return X + Y;
   end Add;

end Swap_Add_05;
