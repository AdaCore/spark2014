pragma Extensions_Allowed (All_Extensions);

procedure Test (B : Boolean; C1, C2 : Integer; O : out Integer) with
  SPARK_Mode,
  Depends => (O => C1, null => (B, C2))
is
   X : Integer := C1;
begin
   <<Inner>>
   if B then
      goto Use_Value;
   end if;

   <<Outer>>
   X := C2;

   <<Use_Value>>
   O := X'At (Inner)'At (Outer);
end Test;
