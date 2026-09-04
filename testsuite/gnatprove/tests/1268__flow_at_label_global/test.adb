pragma Extensions_Allowed (All_Extensions);

procedure Test (C1, C2 : Integer; O : out Integer) with SPARK_Mode,
  Depends => (O => C1, null => C2)
is
   X : Integer := C1;
begin
   <<Init>>
   X := C2;
   declare
      function Snapshot return Integer is (X'At (Init));
   begin
      O := Snapshot;
   end;
end;
