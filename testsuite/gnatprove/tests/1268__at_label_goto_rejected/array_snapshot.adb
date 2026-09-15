pragma Extensions_Allowed (All_Extensions);

procedure Array_Snapshot
  (Before_1, Before_2 :     Integer;
   After_1, After_2   :     Integer;
   O1, O2             : out Integer)
with SPARK_Mode
is
   type Arr is array (1 .. 2) of Integer;

   A : Arr := (Before_1, Before_2);
begin
   goto Capture;

   <<Capture>>
   A := (After_1, After_2);
   O1 := A'At (Capture) (1);
   O2 := A'At (Capture) (2);
end Array_Snapshot;
