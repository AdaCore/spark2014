pragma Extensions_Allowed (All_Extensions);

procedure Test
  (Before_Left, After_Left   : Integer;
   Before_Right, After_Right : Integer;
   Output_Left               : out Integer;
   Output_Right              : out Integer)
with
  SPARK_Mode,
  Depends =>
    (Output_Left  => (Before_Left, Before_Right),
     Output_Right => (Before_Left, Before_Right),
     null         => (After_Left, After_Right))
is
   type Root_Pair is record
      Left  : Integer;
      Right : Integer;
   end record;

   type Pair is new Root_Pair;

   Source : Root_Pair := (Before_Left, Before_Right);
   Saved  : Pair;

begin
   <<Capture>>
   Source := (After_Left, After_Right);
   Saved := Pair (Source)'At (Capture);
   Output_Left := Saved.Left;
   Output_Right := Saved.Right;
end Test;
