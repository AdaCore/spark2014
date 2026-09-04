pragma Extensions_Allowed (All_Extensions);

procedure Mixed_Refs (Input : Integer; Output : out Integer)
with
  SPARK_Mode,
  Depends => (Output => Input)
is
   X : Integer := Input;
   Y : Integer;
begin
   <<Capture>>
   if False then
      Output := Y'At (Capture);
   else
      Output := X'At (Capture);
   end if;
end Mixed_Refs;
