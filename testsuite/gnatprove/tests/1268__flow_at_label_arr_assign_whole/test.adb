pragma Extensions_Allowed (All_Extensions);

procedure Test
  (Before_1, Before_2 :     Integer;
   After_1, After_2   :     Integer;
   O1, O2             : out Integer)
with
  SPARK_Mode,
  Depends =>
    ((O1, O2) => (Before_1, Before_2), null => (After_1, After_2))
is
   type Arr is array (1 .. 2) of Integer;

   A     : Arr := (Before_1, Before_2);
   Saved : Arr;
begin
   <<Capture>>
   A := (After_1, After_2);
   Saved := A'At (Capture);
   O1 := Saved (1);
   O2 := Saved (2);
end Test;
