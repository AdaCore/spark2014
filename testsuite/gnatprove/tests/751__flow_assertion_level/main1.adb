pragma Assertion_Level (L3);
with P; use P;

procedure Main1 is
   X, X1, X2 : Boolean := True;
   Y, Y1, Y2 : Boolean with Ghost;

   X3 : Boolean := True;
   Y3 : Boolean with Ghost => L3;

   procedure Test
      with Pre => True
   is
   begin
      Set_Item  (X);
      Set_Item1 (X1);
      Set_Item2 (X2);

      Flip;

      Y  := Get_Item;
      Y1 := Get_Item1;
      Y2 := Get_Item2;

      Y3 := X3;
   end;
begin
   Test;
end;
