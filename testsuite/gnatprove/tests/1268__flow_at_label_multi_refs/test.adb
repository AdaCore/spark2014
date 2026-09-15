pragma Extensions_Allowed (All_Extensions);

procedure Test (C1, C2, D1, D2 : Integer; O1, O2 : out Integer)
with
  SPARK_Mode,
  Depends => (O1 => C1, O2 => D1, null => (C2, D2))
is
   X : Integer := C1;
   Y : Integer := D1;
begin
   <<Init>>
   X := C2;
   Y := D2;
   O1 := X'At (Init);
   O2 := Y'At (Init);
end;
