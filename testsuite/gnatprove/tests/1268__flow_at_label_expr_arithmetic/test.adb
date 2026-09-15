pragma Extensions_Allowed (All_Extensions);

procedure Test (C1, C2 : Integer; O : out Integer) with
  SPARK_Mode,
  Pre     => C1 > Integer'First and then C2 > Integer'First,
  Depends => (O => C1, null => C2)
is
   X : Integer := C1;
begin
   <<Init>>
   X := C2;
   O := Integer'(X - 1)'At (Init);
end Test;
