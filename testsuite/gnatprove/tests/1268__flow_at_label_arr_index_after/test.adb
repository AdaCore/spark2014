pragma Extensions_Allowed (All_Extensions);

procedure Test
  (Before_1, Before_2 :     Integer;
   After_1, After_2   :     Integer;
   I                  :     Positive;
   O                  : out Integer)
with
  SPARK_Mode,
  Pre     => I in 1 .. 2,
  Depends => (O => (Before_1, Before_2, I), null => (After_1, After_2))
is
   type Arr is array (1 .. 2) of Integer;

   A : Arr := (Before_1, Before_2);
begin
   <<Capture>>
   A := (After_1, After_2);
   O := A'At (Capture) (I);
end Test;
