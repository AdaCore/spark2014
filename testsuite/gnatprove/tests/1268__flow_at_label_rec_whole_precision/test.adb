pragma Extensions_Allowed (All_Extensions);

procedure Test
  (A1, A2 : Integer;
   X1, X2, Y1, Y2 : Boolean;
   O1     : out Integer)
with
  SPARK_Mode,
  Depends => (O1 => A1, null => (A2, X1, X2, Y1, Y2))
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

   Obj   : RR := (A => A1, B => (X => X1, Y => Y1), C => (null record));
   Saved : RR;
begin
   <<Init>>
   Obj.A := A2;
   Obj.B.X := X2;
   Obj.B.Y := Y2;

   Saved := Obj'At (Init);
   O1 := Saved.A;
end;
