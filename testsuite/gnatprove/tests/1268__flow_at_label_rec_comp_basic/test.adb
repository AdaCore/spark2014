pragma Extensions_Allowed (All_Extensions);

procedure Test (X1, X2 : Boolean; O : out Boolean) with SPARK_Mode,
  Depends => (O => X1, null => X2)
is
   type R2 is record
      X : Boolean;
      Y : Boolean;
   end record;

   type R3 is null record;

   type RR is record
      A : Integer;
      B : R2;
      C : R3;
   end record;

   Obj : RR := (A => 0, B => (X => X1, Y => False), C => (null record));
begin
   <<Init>>
   Obj.B.X := X2;
   O := Obj.B.X'At (Init);
end;
