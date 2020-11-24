procedure Update (X : Integer; Y : out Integer)
  with Global  => null,
       Depends => (Y => X),
       Post    => Y = X
is
   type T1 is record
      C1 : Integer;
   end record;

   type T2 is record
      C2 : T1;
   end record;

   Tmp : T2 := (C2 => (C1 => X));
begin
   Tmp := Tmp'Update (C2 => @.C2);

   Y := Tmp.C2.C1;
end;
