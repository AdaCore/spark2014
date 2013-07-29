separate (A)
procedure Swap_B (X, Y : in out Integer)
is
   Tmp : Integer;
begin
   Tmp := X;
   X := Y;
   Y := Tmp;
end Swap_B;
