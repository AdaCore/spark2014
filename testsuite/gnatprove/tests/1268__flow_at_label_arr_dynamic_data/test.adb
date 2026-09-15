pragma Extensions_Allowed (All_Extensions);

procedure Test
  (Low, High     :     Positive;
   Before, After :     Integer;
   I             :     Positive;
   O             : out Integer)
with
  SPARK_Mode,
  Pre     => Low <= High and then High <= 3 and then I in Low .. High,
  Depends => (O => (Low, High, Before, I), null => After)
is
   type Arr is array (Positive range <>) of Integer;

   A : Arr (Low .. High) := (others => Before);
begin
   <<Capture>>
   A := (others => After);
   O := A'At (Capture) (I);
end Test;
