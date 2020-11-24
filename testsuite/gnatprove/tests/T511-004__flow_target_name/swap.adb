procedure Swap (X, Y : in out Integer)
  with Global  => null,
       Depends => (Y => X, X => Y),
       Post    => X = Y'Old and Y = X'Old
is
   type T is record
      A, B : Integer;
   end record;
   Tmp : T := (A => X, B => Y);
begin
   Tmp := (A => @.B, B => @.A);
   X := Tmp.A;
   Y := Tmp.B;
end;
