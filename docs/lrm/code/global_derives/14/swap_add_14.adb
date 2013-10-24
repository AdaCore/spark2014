package body Swap_Add_14 is   
   X, Y: Integer;
   
   procedure Swap is
      Temporary: Integer;
   begin
      Temporary := X;
      X         := Y;
      Y         := Temporary;
   end Swap;

   function Add return Integer is
   begin
      return X + Y;
   end Add;
end Swap_Add_14;
