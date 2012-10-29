package body pre_post_return_05
is   
   X, Y: Integer;
   
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
   
   function Max return Integer
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
   
   function Divide return Float
   is
      Result: Float;
   begin
      Result := Float(X / Y);
      return Result;
   end Divide;
   
   procedure Swap_Array_Elements(A: in out Array_Type)
   is
      Temporary: Integer;
   begin
      Temporary := A(X);
      A(X)      := A(Y);
      A(Y)      := Temporary;
   end Swap_Array_Elements;
   
end pre_post_return_05;
