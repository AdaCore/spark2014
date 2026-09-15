pragma Extensions_Allowed (All_Extensions);

procedure G4
  (X, Z : Integer;
   Y1   : out Integer;
   Y2   : out Integer)
with
  Post    => Y1 = X and Y2 = Z,
  Depends => (Y1 => X, Y2 => Z)
is
   Tmp : Integer := X;
begin
   <<First>>
   Tmp := Z;
   <<Second>>
   Y2 := Tmp;
   Tmp := @'At (First)'At (Second);
   Y1 := Tmp;
end G4;
