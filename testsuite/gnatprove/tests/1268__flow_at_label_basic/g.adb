pragma Extensions_Allowed (All_Extensions);

procedure G (X1, X2 : Integer; Y1, Y2 : out Integer)
   with Post => Y1 = X1 and Y2 = X2,
        Depends => (Y1 => X1, Y2 => X2)
is
   type T is record
      C1, C2 : Integer;
   end record;
   Tmp : T;
begin
   Tmp := (X1,X2);
   <<L>>
   Tmp := Tmp'At (L);
   Y1 := Tmp.C1;
   Y2 := Tmp.C2;
end;
