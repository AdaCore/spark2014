pragma Extensions_Allowed (All_Extensions);

procedure Test
  (A                   :     String;
   First, Last, Length : out Integer)
with
  SPARK_Mode,
  Depends => ((First, Last, Length) => A)
is
begin
   <<Capture>>
   First := A'At (Capture)'First;
   Last := A'At (Capture)'Last;
   Length := A'At (Capture)'Length;
end Test;
