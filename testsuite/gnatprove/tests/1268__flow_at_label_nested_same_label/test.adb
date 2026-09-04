pragma Extensions_Allowed (All_Extensions);

procedure Test (C1, C2 : Integer; O : out Integer) with
  SPARK_Mode,
  Depends => (O => C1, null => C2)
is
   X : Integer := C1;
begin
   <<Capture>>
   X := C2;
   O := X'At (Capture)'At (Capture);
end Test;
