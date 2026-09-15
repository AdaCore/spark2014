pragma Extensions_Allowed (All_Extensions);

procedure Test1 (C1, C2, C3 : Integer; O1, O2 : out Integer) with
  SPARK_Mode,
  Depends => (O1 => C1, O2 => C2, null => C3)
is
   X : Integer := C1;
begin
   <<First>>
   X := C2;
   <<Second>>
   X := C3;
   O1 := X'At (First);
   O2 := X'At (Second);
end;
