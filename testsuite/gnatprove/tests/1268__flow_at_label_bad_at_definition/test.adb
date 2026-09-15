pragma Extensions_Allowed (All_Extensions);

procedure Test (C : Integer; O : out Integer) with SPARK_Mode
is
   X : Integer;
begin
   <<Init>>
   X := C;
   O := X'At (Init);
end;
