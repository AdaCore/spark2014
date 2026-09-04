pragma Extensions_Allowed (All_Extensions);

procedure Test
  (Before_Left, After_Left   : Integer;
   Before_Right, After_Right : Integer;
   Snapshot_Output            : out Integer;
   Current_Output             : out Integer)
with
  SPARK_Mode,
  Depends =>
    (Snapshot_Output => (Before_Left, Before_Right),
     Current_Output  => (After_Left, After_Right))
is
   type Pair is record
      Left  : Integer;
      Right : Integer;
   end record;

   function Make_Pair (Left, Right : Integer) return Pair
   with Depends => (Make_Pair'Result => (Left, Right));

   function Make_Pair (Left, Right : Integer) return Pair is
     (Left => Left, Right => Right);

   Left  : Integer := Before_Left;
   Right : Integer := Before_Right;

begin
   <<Capture>>
   Left := After_Left;
   Right := After_Right;
   Snapshot_Output := Make_Pair (Left, Right)'At (Capture).Left;
   Current_Output := Make_Pair (Left, Right).Left;
end Test;
