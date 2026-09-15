pragma Extensions_Allowed (All_Extensions);

procedure Test (C1, C2, Noise : Integer; O : out Integer) with
  SPARK_Mode,
  Depends => (O => C1, null => (C2, Noise))
is
   function Pick (V, N : Integer) return Integer with
     Depends => (Pick'Result => V, null => N);

   function Pick (V, N : Integer) return Integer is (V);

   X : Integer := C1;
begin
   <<Init>>
   X := C2;
   O := Pick (X'At (Init), Noise);
end;
