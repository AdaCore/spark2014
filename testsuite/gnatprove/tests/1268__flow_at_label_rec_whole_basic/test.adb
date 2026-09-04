pragma Extensions_Allowed (All_Extensions);

procedure Test
  (A1, A2 : Integer;
   X1, X2, Y1, Y2 : Boolean;
   O1     : out Integer;
   O2, O3 : out Boolean)
with
  SPARK_Mode,
  Depends => (O1 => A1, O2 => X1, O3 => Y1, null => (A2, X2, Y2))
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

   Obj : RR := (A => A1, B => (X => X1, Y => Y1), C => (null record));
begin
   <<Init>>
   Obj.A := A2;
   Obj.B.X := X2;
   Obj.B.Y := Y2;
   O1 := Obj'At (Init).A;
   O2 := Obj'At (Init).B.X;
   O3 := Obj'At (Init).B.Y;
end;
