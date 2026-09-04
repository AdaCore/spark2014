pragma Extensions_Allowed (All_Extensions);

procedure G3 (X : Integer; Y : out Integer)
  with Post => Y = X,
       Depends => (Y => X)
is
   type Rec is record
      A : Integer;
      B : Integer;
   end record;

   R : Rec := (A => X, B => 0);
begin
   <<L>>
   R := Rec'(@ with delta B => 1)'At (L);
   Y := R.A;
end G3;
