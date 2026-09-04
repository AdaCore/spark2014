pragma Extensions_Allowed (All_Extensions);

procedure Test (C1, C2, D1, D2 : Integer; O1, O2 : out Integer)
with
  SPARK_Mode,
  Depends => (O1 => C1, O2 => D1, null => (C2, D2))
is
   type Inner is record
      A : Integer;
      B : Integer;
   end record;

   type Outer is record
      F : Inner;
   end record;

   R : Outer := (F => (A => C1, B => D1));
begin
   <<Init>>
   R.F.A := C2;
   R.F.B := D2;
   O1 := R.F'At (Init).A;
   O2 := R.F'At (Init).B;
end;
