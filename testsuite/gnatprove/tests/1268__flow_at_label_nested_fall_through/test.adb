pragma Extensions_Allowed (All_Extensions);

procedure Test (C1, C2, C3 : Integer; O : out Integer) with SPARK_Mode,
  Depends => (O => C1, null => (C2, C3))
is
   X : Integer := C1;
begin
   <<First>>
   X := C2;
   <<Second>>
   X := C3;
   O := X'At (First)'At (Second);
end;
