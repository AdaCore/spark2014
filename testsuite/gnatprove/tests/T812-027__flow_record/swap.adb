procedure Swap (X, Y : in out Integer)
  with Depends => (X => Y, Y => X),
       Post    => X = Y'Old and Y = X'Old
is
   type T is record A, B : Integer; end record;
   Tmp : T := (A => X, B => Y);
begin
   Tmp := (A => Tmp.B, B => Tmp.A);
   X := Tmp.A;
   Y := Tmp.B;
end;
