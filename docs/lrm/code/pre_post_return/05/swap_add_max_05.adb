package body Swap_Add_Max_05
is
   procedure Swap (X, Y: in out Integer)
   is
      Temporary: Integer;
   begin
      Temporary := X;
      X         := Y;
      Y         := Temporary;
   end Swap;

   function Add (X, Y : Integer) return Integer
   is
   begin
      return X + Y;
   end Add;

   function Max (X, Y : Integer) return Integer
   is
      Result: Integer;
   begin
      if X >= Y then
         Result := X;
      else
         Result := Y;
      end if;
      return Result;
   end Max;

   function Divide (X, Y : Integer) return Integer
   is
   begin
      return X / Y;
   end Divide;

   procedure Swap_Array_Elements(I, J : Index; A: in out Array_Type)
   is
      Temporary: Integer;
   begin
      Temporary := A(I);
      A(I)      := A(J);
      A(J)      := Temporary;
   end Swap_Array_Elements;

end Swap_Add_Max_05;
