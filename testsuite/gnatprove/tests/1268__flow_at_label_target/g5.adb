pragma Extensions_Allowed (All_Extensions);

procedure G5 (X, Z : Integer; Y : out Integer)
with
  Pre     => X in -1_000 .. 1_000 and Z in -1_000 .. 1_000,
  Post    => Y = X + Z,
  Depends => (Y => (X, Z))
is
   Tmp : Integer := X;
begin
   <<First>>
   Tmp := Z;
   <<Second>>
   Tmp := Integer'(@ + @'At (First))'At (Second);
   Y := Tmp;
end G5;
