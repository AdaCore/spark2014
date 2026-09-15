pragma Extensions_Allowed (All_Extensions);

procedure Test
  (A1, A2 : Integer;
   X1, X2, Y1, Y2 : Boolean;
   O2, O3 : out Boolean)
with
  SPARK_Mode,
  Depends => (O2 => X1, O3 => Y1, null => (A1, A2, X2, Y2))
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

   Obj     : RR := (A => A1, B => (X => X1, Y => Y1), C => (null record));
   Saved_B : R2;
begin
   <<Init>>
   Obj.A := A2;
   Obj.B.X := X2;
   Obj.B.Y := Y2;

   Saved_B := Obj'At (Init).B;
   O2 := Saved_B.X;
   O3 := Saved_B.Y;
end;
