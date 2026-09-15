pragma Extensions_Allowed (All_Extensions);

procedure Test
  (Before_1, Before_2, Before_3 :     Integer;
   After_1, After_2, After_3    :     Integer;
   Low, High                    :     Positive;
   I                            :     Positive;
   O                            : out Integer)
with
  SPARK_Mode,
  Pre =>
    Low in 1 .. 3
    and then High in 1 .. 3
    and then Low <= High
    and then I in Low .. High,
  Depends =>
    (O    => (Before_1, Before_2, Before_3, Low, High, I),
     null => (After_1, After_2, After_3))
is
   type Arr is array (Positive range 1 .. 3) of Integer;

   A : Arr := (Before_1, Before_2, Before_3);
begin
   <<Capture>>
   A := (After_1, After_2, After_3);
   O := A'At (Capture) (Low .. High) (I);
end Test;
