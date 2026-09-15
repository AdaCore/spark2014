pragma Extensions_Allowed (All_Extensions);

procedure G2 (X : Integer; Y : out Integer)
   with Post => Y = X,
        Depends => (Y => X)
is
   Tmp : Integer;
begin
   Tmp := X;
   <<L>>
   Y := @'At (L);
end;
