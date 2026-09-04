pragma Extensions_Allowed (All_Extensions);

procedure Test (C1, C2 : Integer; O : out Integer) with SPARK_Mode,
  Depends => (O => C1, null => C2)
is
   function Id (V : Integer) return Integer is (V);

   X : Integer := C1;
begin
   <<Init>>
   X := C2;
   O := Id (X)'At (Init);
end;
