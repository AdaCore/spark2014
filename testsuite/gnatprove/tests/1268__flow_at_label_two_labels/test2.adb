pragma Extensions_Allowed (All_Extensions);

procedure Test2 (C : Integer; O1, O2 : out Integer) with SPARK_Mode
is
   X : Integer;
begin
   <<Bad>>
   X := C;
   <<Good>>

   O1 := X'At (Good);
   O2 := X'At (Bad);
end;
