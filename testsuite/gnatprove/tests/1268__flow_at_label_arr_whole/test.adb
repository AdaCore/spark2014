pragma Extensions_Allowed (All_Extensions);

procedure Test (C1, C2, D1, D2 : Integer; O1, O2 : out Integer)
with
  SPARK_Mode,
  Depends => ((O1, O2) => (C1, D1), null => (C2, D2))
is
   type Arr is array (1 .. 2) of Integer;

   A : Arr := (1 => C1, 2 => D1);
begin
   <<Init>>
   A (1) := C2;
   A (2) := D2;
   O1 := A'At (Init) (1);
   O2 := A'At (Init) (2);
end;
