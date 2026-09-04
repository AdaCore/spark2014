pragma Extensions_Allowed (All_Extensions);

procedure Test
  (B1, B2         : Boolean;
   C1, C2, C3, C4 : Integer;
   Output         : out Integer)
with
  SPARK_Mode,
  Depends => (Output => (B1, C1, C4), null => (B2, C2, C3))
is
   B : Boolean := B1;
   X : Integer := C1;
begin
   <<First>>
   X := C2;
   <<Second>>
   B := B2;
   X := C3;
   Output := Integer ((if B then X'At (First) else C4))'At (Second);
end Test;
