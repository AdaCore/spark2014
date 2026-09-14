pragma Extensions_Allowed (All_Extensions);

procedure Test
  (Before_Left, After_Left   : Integer;
   Before_Right, After_Right : Integer;
   Output_Left               : out Integer;
   Output_Right              : out Integer)
with
  SPARK_Mode,
  Depends =>
    (Output_Left  => Before_Left,
     Output_Right => Before_Right,
     null         => (After_Left, After_Right))
is
   type Pair is record
      Left  : Integer;
      Right : Integer;
   end record;

   Source : Pair := (Left => Before_Left, Right => Before_Right);
   Saved  : Pair;

begin
   <<Capture>>
   Source := (Left => After_Left, Right => After_Right);
   Saved := Pair'(Source)'At (Capture);
   Output_Left := Saved.Left;
   Output_Right := Saved.Right;
end Test;
