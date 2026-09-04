pragma Extensions_Allowed (All_Extensions);

procedure Test
  (A1, A2 : Integer;
   X1, X2 : Boolean;
   O1, C1 : out Integer;
   O2, C2 : out Boolean)
with
  SPARK_Mode,
  Depends =>
    ((O1, O2) => (A1, X1),
     (C1, C2) => (A2, X2))
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

   function Pick_A (R : RR) return Integer is (R.A);

   function Pick_X (R : RR) return Boolean is (R.B.X);

   Obj : RR := (A => A1, B => (X => X1, Y => False), C => (null record));
begin
   <<Init>>
   Obj.A := A2;
   Obj.B.X := X2;

   O1 := Pick_A (Obj'At (Init));
   O2 := Pick_X (Obj'At (Init));
   C1 := Pick_A (Obj);
   C2 := Pick_X (Obj);
end;
