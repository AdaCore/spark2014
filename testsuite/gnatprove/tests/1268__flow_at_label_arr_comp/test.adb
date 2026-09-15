pragma Extensions_Allowed (All_Extensions);

procedure Test (C1, C2 : Integer; O : out Integer) with SPARK_Mode,
  Depends => (O => C1, null => C2)
is
   type Arr is array (1 .. 2) of Integer;

   A : Arr := (1 => C1, 2 => 0);
begin
   <<Init>>
   A (1) := C2;
   O := A (1)'At (Init);
end;
