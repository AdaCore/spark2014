pragma Extensions_Allowed (All_Extensions);

procedure Test
  (A : in out String;
   V :        Character;
   O :    out Character)
with
  SPARK_Mode,
  Pre     => A'Length > 0,
  Depends => (A =>+ V, O => A)
is
begin
   <<Capture>>
   A (A'First) := V;
   O := A'At (Capture) (A'First);
end Test;
